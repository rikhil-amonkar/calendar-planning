from z3 import *

def main():
    # Create solver
    s = Solver()

    # City indices: Geneva=0, Paris=1, Oslo=2, Porto=3, Reykjavik=4
    # Define variables for intermediate cities and travel days
    cityA = Int('cityA')
    cityB = Int('cityB')
    cityC = Int('cityC')
    x = Int('x')  # day we leave cityA (and arrive in cityB)
    y = Int('y')  # day we leave cityB (and arrive in cityC)

    # Constraints for cityA, cityB, cityC: must be Paris(1), Porto(3), or Reykjavik(4)
    s.add(cityA >= 1, cityA <= 4, cityA != 2)  # not Oslo(2) or Geneva(0)
    s.add(cityB >= 1, cityB <= 4, cityB != 2)
    s.add(cityC >= 1, cityC <= 4, cityC != 2)
    s.add(Distinct(cityA, cityB, cityC))

    # Flight constraints
    # From Geneva(0) to cityA: only Paris(1) or Porto(3)
    s.add(Or(cityA == 1, cityA == 3))

    # From cityA to cityB
    s.add(
        Or(
            And(cityA == 1, Or(cityB == 3, cityB == 4)),
            And(cityA == 3, cityB == 1)
        )
    )

    # From cityB to cityC: avoid (Porto to Reykjavik) and (Reykjavik to Porto)
    s.add(
        Or(
            And(cityB == 1, Or(cityC == 3, cityC == 4)),
            And(cityB == 3, cityC == 1),
            And(cityB == 4, cityC == 1)
        )
    )

    # Stay constraints
    stayA = x - 6  # because stay in cityA is from day7 to day x (inclusive): (x - 7 + 1) = x - 6
    s.add(
        If(cityA == 1, stayA == 6,
           If(cityA == 3, stayA == 7,
              stayA == 2  # if cityA==4
           )
        )
    )

    stayB = y - x + 1  # from day x to day y (inclusive)
    s.add(
        If(cityB == 1, stayB == 6,
           If(cityB == 3, stayB == 7,
              stayB == 2  # if cityB==4
           )
        )
    )

    stayC = 20 - y  # from day y to day 19 (inclusive): 19 - y + 1 = 20 - y
    s.add(
        If(cityC == 1, stayC == 6,
           If(cityC == 3, stayC == 7,
              stayC == 2  # if cityC==4
           )
        )
    )

    # Constraints on x and y
    s.add(x >= 7, x <= 18)
    s.add(y >= x, y <= 19)

    # Check and get model
    if s.check() == sat:
        m = s.model()
        cityA_val = m[cityA].as_long()
        cityB_val = m[cityB].as_long()
        cityC_val = m[cityC].as_long()
        x_val = m[x].as_long()
        y_val = m[y].as_long()

        # Map city indices to names
        mapping = {1: "Paris", 3: "Porto", 4: "Reykjavik"}

        # Build itinerary
        itinerary = [
            {"day_range": "Day 1-7", "place": "Geneva"},
            {"day_range": "Day 7", "place": "Geneva"},
            {"day_range": "Day 7", "place": mapping[cityA_val]},
            {"day_range": f"Day 7-{x_val}", "place": mapping[cityA_val]},
            {"day_range": f"Day {x_val}", "place": mapping[cityA_val]},
            {"day_range": f"Day {x_val}", "place": mapping[cityB_val]},
            {"day_range": f"Day {x_val}-{y_val}", "place": mapping[cityB_val]},
            {"day_range": f"Day {y_val}", "place": mapping[cityB_val]},
            {"day_range": f"Day {y_val}", "place": mapping[cityC_val]},
            {"day_range": f"Day {y_val}-19", "place": mapping[cityC_val]},
            {"day_range": "Day 19", "place": mapping[cityC_val]},
            {"day_range": "Day 19", "place": "Oslo"},
            {"day_range": "Day 19-23", "place": "Oslo"}
        ]

        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()