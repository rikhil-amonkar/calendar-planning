# Solve the 20-day, 10-city itinerary with overlap-on-flight-day counting using Z3
# and print a JSON-formatted dictionary with an 'itinerary' key.

from z3 import Solver, IntVector, Or, And, If, Sum
import json
import re

# Cities and required total days (with overlap rule)
cities = [
    "Prague", "Brussels", "Riga", "Munich", "Seville",
    "Stockholm", "Istanbul", "Amsterdam", "Vienna", "Split"
]
city_idx = {c: i for i, c in enumerate(cities)}

required_days = {
    "Prague": 5,
    "Brussels": 2,
    "Riga": 2,
    "Munich": 2,
    "Seville": 3,
    "Stockholm": 2,
    "Istanbul": 2,
    "Amsterdam": 3,
    "Vienna": 5,
    "Split": 3
}

# Direct flights specification (directed if "from X to Y", undirected if "X and Y")
edges_text = """
Riga and Stockholm, Stockholm and Brussels, Istanbul and Munich, Istanbul and Riga, Prague and Split,
Vienna and Brussels, Vienna and Riga, Split and Stockholm, Munich and Amsterdam, Split and Amsterdam,
Amsterdam and Stockholm, Amsterdam and Riga, Vienna and Stockholm, Vienna and Istanbul, Vienna and Seville,
Istanbul and Amsterdam, Munich and Brussels, Prague and Munich, from Riga to Munich, Prague and Amsterdam,
Prague and Brussels, Prague and Istanbul, Istanbul and Stockholm, Vienna and Prague, Munich and Split,
Vienna and Amsterdam, Prague and Stockholm, Brussels and Seville, Munich and Stockholm, Istanbul and Brussels,
Amsterdam and Seville, Vienna and Split, Munich and Seville, Riga and Brussels, Prague and Riga, Vienna and Munich.
"""

def parse_edges(edges_text, cities_set):
    pairs = set()
    # split on commas, strip whitespace and trailing periods
    parts = [p.strip().rstrip('.') for p in edges_text.split(',') if p.strip()]
    for p in parts:
        # normalize whitespace
        p = re.sub(r'\s+', ' ', p.strip())
        if not p:
            continue
        if p.lower().startswith("from "):
            # pattern: from X to Y
            m = re.match(r'from (.+?) to (.+)$', p, flags=re.IGNORECASE)
            if not m:
                continue
            a = m.group(1).strip()
            b = m.group(2).strip()
            if a in cities_set and b in cities_set:
                pairs.add((a, b))
        else:
            # pattern: X and Y
            m = re.match(r'(.+?) and (.+)$', p, flags=re.IGNORECASE)
            if not m:
                continue
            a = m.group(1).strip()
            b = m.group(2).strip()
            if a in cities_set and b in cities_set:
                pairs.add((a, b))
                pairs.add((b, a))
    return pairs

edges_str_pairs = parse_edges(edges_text, set(cities))
edges = {(city_idx[a], city_idx[b]) for (a, b) in edges_str_pairs}

# Z3 setup
DAYS = 20
day_vars = IntVector('day', DAYS)  # day_vars[0] is Day 1, ..., day_vars[19] is Day 20
s = Solver()

# Domain: day_vars[t] is an index 0..len(cities)-1
for t in range(DAYS):
    s.add(day_vars[t] >= 0, day_vars[t] < len(cities))

# Flight adjacency constraint: If we change cities on day t (t>=2), the pair must be a direct flight (prev -> current)
for t in range(1, DAYS):
    # Either same city as previous day, or a direct flight exists from previous to current.
    same = day_vars[t] == day_vars[t-1]
    allowed_flights = Or([And(day_vars[t-1] == a, day_vars[t] == b) for (a, b) in edges]) if edges else False
    s.add(Or(same, allowed_flights))

# Helper to express "presence in city c on calendar day t (1-indexed)" with overlap rule:
# Present on day t if:
# - city[t] == c, OR
# - t>1 and city[t-1] == c and city[t] != city[t-1]  (i.e., departed from c on day t)
def presence_expr(c_idx, t):
    # t is 1..DAYS
    if t == 1:
        return day_vars[0] == c_idx
    else:
        return Or(
            day_vars[t-1] == c_idx,
            And(day_vars[t-2] == c_idx, day_vars[t-1] != day_vars[t-2])
        )

# Exact required days per city with the overlap rule
for cname, req in required_days.items():
    c = city_idx[cname]
    s.add(Sum([If(presence_expr(c, t+1), 1, 0) for t in range(DAYS)]) == req)

# Event/meeting window constraints (presence with overlap rule)
# Prague show days 5..9 inclusive: must be present each day
prague = city_idx["Prague"]
for d in range(5, 10):
    s.add(presence_expr(prague, d))

# Stockholm conference days 16 and 17: must be present each day
stockholm = city_idx["Stockholm"]
for d in [16, 17]:
    s.add(presence_expr(stockholm, d))

# Meet a friend in Vienna between day 1 and day 5: at least one day presence
vienna = city_idx["Vienna"]
s.add(Or([presence_expr(vienna, d) for d in range(1, 6)]))

# Meet friends in Riga between day 15 and day 16: at least one day presence
riga = city_idx["Riga"]
s.add(Or(presence_expr(riga, 15), presence_expr(riga, 16)))

# Visit relatives in Split between day 11 and day 13: at least one day presence
split = city_idx["Split"]
s.add(Or([presence_expr(split, d) for d in range(11, 14)]))

# Solve
if s.check() != 1:
    raise RuntimeError("No feasible itinerary found under given constraints.")

m = s.model()
itinerary = []
for d in range(1, DAYS + 1):
    cid = m.eval(day_vars[d-1]).as_long()
    itinerary.append({"day": d, "city": cities[cid]})

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))