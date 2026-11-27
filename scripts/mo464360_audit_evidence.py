"""Recheck public metadata and OEIS catalogue evidence for MathOverflow 464360."""
from datetime import datetime, timezone
from gzip import GzipFile
from pathlib import Path
from urllib.parse import urlencode
from urllib.request import Request, urlopen
import json

ROOT = Path(__file__).resolve().parent
SITE = "mathoverflow"
QUESTION = "464360"
OEIS_DISTRIBUTION = "https://oeis.org/stripped.gz"
OEIS_ENTRY = "https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A110/A110978.seq"


def fetch(url):
    return urlopen(Request(url, headers={"User-Agent": "Public mathematics source check"}), timeout=45)


def stack(site, method, **params):
    url = f"https://api.stackexchange.com/2.3/{method}?" + urlencode(
        {"site": site, "pagesize": 100, **params}
    )
    with fetch(url) as response:
        data = json.load(response)
    return {"url": url, "has_more": data["has_more"], "items": data["items"]}


def prefix_from_loop(count):
    terms = []
    n = 0
    while len(terms) < count:
        x = n
        while x < 2*n:
            low = x & -x
            x += min(low, x // low)
        if x == 2*n + 1:
            terms.append(x)
        n += 1
    return terms


def collect():
    question = stack(SITE, f"questions/{QUESTION}")
    q = question["items"][0]
    info = {
        "checked_utc": datetime.now(timezone.utc).isoformat(),
        "question": {k: q[k] for k in ("question_id", "title", "link", "answer_count",
                                        "is_answered", "creation_date", "last_activity_date")},
        "closure_recorded": "closed_date" in q,
        "thread_api": question["url"],
    }
    for name in ("answers", "comments", "linked", "related"):
        result = stack(SITE, f"questions/{QUESTION}/{name}")
        info[name] = {
            "url": result["url"],
            "has_more": result["has_more"],
            "count": len(result["items"]),
            "ids": [item.get("question_id", item.get("comment_id")) for item in result["items"]],
        }
    info["stack_search"] = {}
    for site in ("mathoverflow", "math"):
        result = stack(site, "search/advanced", q="A110978")
        info["stack_search"][site] = {
            "url": result["url"], "has_more": result["has_more"],
            "ids": [q["question_id"] for q in result["items"]],
        }

    openalex_url = "https://api.openalex.org/works?" + urlencode({"search": "A110978", "per_page": 10})
    with fetch(openalex_url) as response:
        info["openalex"] = {"url": openalex_url, "count": json.load(response)["meta"]["count"]}

    prefix = prefix_from_loop(12)
    needle = ("," + ",".join(map(str, prefix)) + ",").encode("ascii")
    count = 0
    target_found = False
    matches = []
    with fetch(OEIS_DISTRIBUTION) as response, GzipFile(fileobj=response) as stream:
        for line in stream:
            if line.startswith(b"A"):
                count += 1
                target_found |= line.startswith(b"A110978 ")
                if needle in line:
                    matches.append(line.split(None, 1)[0].decode("ascii"))
    info["oeis_term_search"] = {
        "url": OEIS_DISTRIBUTION, "entry_count": count, "target_entry_present": target_found,
        "contiguous_terms_sought": prefix, "matching_entries": matches,
    }
    with fetch(OEIS_ENTRY) as response:
        text = response.read().decode("utf-8")
        info["oeis_entry"] = {
            "url": OEIS_ENTRY,
            "contains_sequence_reference": "464360" in text,
            "record_header": text.splitlines()[0],
        }
    return info


if __name__ == "__main__":
    result = collect()
    (ROOT / "status.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
