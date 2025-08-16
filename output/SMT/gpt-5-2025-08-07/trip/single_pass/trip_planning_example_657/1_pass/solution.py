from z3 import Solver, Int, And, Or, Implies, If, Sum, sat
import json

def solve_itinerary():
    # Cities and indices
    cities = ["Frankfurt", "Manchester", "Valencia", "Naples", "Oslo", "Vilnius"]
    FRA, MAN, VLC, NAP, OSL, VNO = range(6)

    # Target days per city (counting flight days for both departure and arrival cities)
    targets = {
        FRA: 4,
        MAN: 4,
        VLC: 4,
        NAP: 4,
        OSL: 3,
        VNO: 2,
    }

    # Allowed direct flight pairs (undirected)
    direct_pairs = {
        (VLC, FRA), (FRA, VLC),
        (MAN, FRA), (FRA, MAN),
        (NAP, MAN), (MAN, NAP),
        (NAP, FRA), (FRA, NAP),
        (NAP, OSL), (OSL, NAP),
        (OSL, FRA), (FRA, OSL),
        (VNO, FRA), (FRA, VNO),
        (OSL, VNO), (VNO, OSL),
        (MAN, OSL), (OSL, MAN),
        (VLC, NAP), (NAP, VLC),
    }

    num_days = 16

    # Decision variables: S[d] is the city index assigned on day d (1-based in description, 0-based in code)
    S = [Int(f"day_{d}") for d in range(1, num_days + 1)]

    solver = Solver()

    # Domain constraints
    for d in range(num_days):
        solver.add(And(S[d] >= 0, S[d] < len(cities)))

    # Direct flights constraints: if city changes from day d-1 to day d, it must be a direct flight
    for d in range(1, num_days):
        prev_city = S[d - 1]
        curr_city = S[d]
        solver.add(
            Implies(
                prev_city != curr_city,
                Or(*[And(prev_city == a, curr_city == b) for (a, b) in direct_pairs])
            )
        )

    # Helper: presence(city c, day d) is True if day d counts for city c
    # A day d counts for city c if:
    # - You are assigned to c on day d, OR
    # - You depart from c on day d (i.e., day d-1 was c and day d is not c).
    def presence(c, d):
        # d is 1..16 for this helper
        idx = d - 1  # 0-based index for S
        if d == 1:
            return S[0] == c
        else:
            return Or(S[idx] == c, And(S[idx - 1] == c, S[idx] != c))

    # Duration constraints: sum of presence over all days equals target for each city
    for c, t in targets.items():
        solver.add(Sum([If(presence(c, d), 1, 0) for d in range(1, num_days + 1)]) == t)

    # Event constraints:
    # - Annual show in Frankfurt from day 13 to day 16: be in Frankfurt on days 13..16
    for d in range(13, 17):
        solver.add(S[d - 1] == FRA)

    # - Wedding in Vilnius between day 12 and day 13: be in Vilnius on day 12 and day 13 (counting presence)
    solver.add(presence(VNO, 12))
    solver.add(presence(VNO, 13))

    # Solve
    if solver.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    model = solver.model()

    itinerary = []
    for d in range(1, num_days + 1):
        city_idx = model[S[d - 1]].as_long()
        itinerary.append({"day": d, "city": cities[city_idx]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))