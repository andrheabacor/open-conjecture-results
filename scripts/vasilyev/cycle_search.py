"""Search the finite induced up-down graph, then validate certificates exactly."""
import argparse
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).parent
sys.path.insert(0, str(ROOT / "search_deps"))

def steps(x):
    return ((x+1)//2, (3*x+1)//2)

def small_check():
    # Generate simple paths from their least vertex. The source maximum 242
    # for length 8 suffices to encompass all cycles in the selected table rows.
    by_length = {i:[] for i in range(1,9)}
    def visit(path):
        for y in steps(path[-1]):
            if y == path[0]:
                by_length[len(path)].append(tuple(path))
            elif y > path[0] and y <= 242 and y not in path and len(path) < 8:
                visit(path+[y])
    for x in range(1,243): visit([x])
    for n,count,largest in [(1,1,1),(2,3,5),(5,12,26),(8,140,242)]:
        cycles = by_length[n]
        assert len(cycles) == count and max(map(max,cycles)) == largest
        print("Table length/count/largest:", n,count,largest)

def check(cycle):
    # Reconstruct the deterministic map via its up set and compare the orbit.
    assert len(set(cycle)) == len(cycle) and min(cycle) > 0
    target = cycle[1:]+cycle[:1]
    up_set = {x for x,y in zip(cycle,target) if y>x}
    x = cycle[0]
    for y in target:
        factor = 3 if x in up_set else 1
        q,r = divmod(factor*x,2)
        x = q+int(r != 0)
        assert x == y
    return len(cycle),len(up_set)

def solve(bound,seconds,seed,focus,threshold,save_result):
    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    arcs = []
    values = []
    scale = 10**7
    for x in range(2,bound+1):
        unused = model.new_bool_var(f"omit{x}")
        arcs.append((x-2,x-2,unused))
        if x == focus: model.add(unused==0)
        for j,y in enumerate(steps(x)):
            if y<2 or y>bound: continue
            flag = model.new_bool_var(f"e{x}_{y}")
            arcs.append((x-2,y-2,flag))
            # Per edge rounding slack is <1/scale. For a true cycle these
            # positive summands telescope to log(2^length/3^up).
            weight = math.floor(scale*math.log1p((x%2)/((2*j+1)*x)))
            values.append((x,y,flag,weight))
    model.add_circuit(arcs)
    total = sum(flag*w for x,y,flag,w in values)
    model.add(total >= math.ceil(scale*math.log(threshold)))
    solver = cp_model.CpSolver()
    solver.parameters.num_workers = 3
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.random_seed = seed
    status = solver.solve(model)
    print("N",bound,"status",solver.status_name(status),"seconds",round(solver.wall_time,2),flush=True)
    if status not in (cp_model.OPTIMAL,cp_model.FEASIBLE): return False
    edges = {x:y for x,y,flag,w in values if solver.value(flag)}
    start = min(edges)
    cycle = [start]
    while edges[cycle[-1]]!=start: cycle.append(edges[cycle[-1]])
    assert len(cycle)==len(edges)
    ell,a = check(cycle)
    print("length",ell,"up",a,"max",max(cycle),"ratio",(2**ell)/(3**a),flush=True)
    if 2**ell >= 3**(a+1):
        if save_result:
            (ROOT/"new_search_cycle.json").write_text(json.dumps(cycle),encoding="utf-8")
        return True
    return False

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--limits",default="")
    p.add_argument("--seconds",type=float,default=40)
    p.add_argument("--seed",type=int,default=7)
    p.add_argument("--focus",type=int,default=0)
    p.add_argument("--threshold",type=float,default=3)
    p.add_argument("--save-result",action="store_true",help="write a new search result to new_search_cycle.json")
    args=p.parse_args()
    small_check()
    for bound in map(int,filter(None,args.limits.split(","))):
        if solve(bound,args.seconds,args.seed,args.focus,args.threshold,args.save_result): break
