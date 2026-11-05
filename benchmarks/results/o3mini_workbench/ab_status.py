import re, collections, os, sys
S = os.path.dirname(os.path.abspath(__file__))
for arm in ('ctrl', 'rc2'):
    for st in ('he', 've'):
        p = os.path.join(S, 'ab', f'{arm}_{st}.log')
        t = open(p, encoding='utf8', errors='replace').read() if os.path.exists(p) else ''
        tr = re.findall(r'^(\S+)\s+trial (\d)\s+(\w+)', t, flags=re.M)
        c = collections.Counter(o for _, _, o in tr)
        cost = re.findall(r'Cumulative Total: \$([0-9.]+)', t)
        net = len(re.findall(r'HTTP 4\d\d|HTTP 5\d\d|returned HTTP', t))
        other = sum(v for k, v in c.items() if k not in ('SOLVED', 'EXHAUSTED'))
        print(f"{'OLD' if arm == 'ctrl' else 'NEW'} {st}: {len(tr):2d}/48 trials  solved={c['SOLVED']:2d} exhausted={c['EXHAUSTED']:2d} other={other}  cost=${cost[-1] if cost else '0'}  tracebacks={t.count('Traceback')} http_errors={net}")
