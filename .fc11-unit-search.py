from __future__ import annotations

import concurrent.futures
import datetime
import json
from pathlib import Path
import sys
import urllib.request

SCRATCH = Path('/tmp/fc11-continuation')
OUT = SCRATCH / 'unit-search'
OUT.mkdir(exist_ok=True)
units = json.loads((SCRATCH / 'units.json').read_text())
chapters = set(sys.argv[1:]) if len(sys.argv) > 1 else None

def one(unit: dict) -> tuple[str, int | str]:
    uid = unit['id']
    if chapters and unit['chapter'] not in chapters:
        return uid, 'skip'
    path = OUT / f'{uid}.json'
    if path.exists():
        return uid, 'cached'
    query = ' '.join(unit['data'].split())
    body = json.dumps({'query': [query], 'num_results': 12}).encode()
    req = urllib.request.Request(
        'https://leansearch.net/search', body,
        {'Content-Type': 'application/json', 'accept': 'application/json',
         'User-Agent': 'LeanCategories-FoundationalCorpusSweep'})
    try:
        with urllib.request.urlopen(req, timeout=45) as response:
            data = response.read().decode()
            status = response.status
    except Exception as exc:
        data = str(exc)
        status = 'ERROR'
    path.write_text(json.dumps({
        'date': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'id': uid,
        'query': query,
        'status': status,
        'response': data,
    }, ensure_ascii=False, indent=2))
    return uid, status

selected = [u for u in units if u['chapter'] != 'C01' and (not chapters or u['chapter'] in chapters)]
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
    for i, (uid, status) in enumerate(pool.map(one, selected), 1):
        if i % 25 == 0 or status == 'ERROR':
            print(i, '/', len(selected), uid, status, flush=True)
