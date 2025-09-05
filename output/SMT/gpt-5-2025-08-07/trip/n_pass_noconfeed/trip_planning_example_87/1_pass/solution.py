import json
from z3 import *

def main():
    # Problem parameters (as variables)
    n_days = 7
    city_names = ["Riga", "Amsterdam", "Mykonos"]
    RIGA, AMS, MYK = 0, 1, 2

    # Required days in each city
    required_days = {
        RIGA: 2,
        AMS: 2,
        MYK: 5
    }

    # Direct flight pairs (both directions)
    direct_flights = set([
        (AMS, MYK), (MYK, AMS),
        (RIGA, AMS), (AMS, RIGA)
    ])

    # Z3 variables
    StartCity = [Int(f"start_{d}") for d in range(1, n_days + 1)]
    DestCity = [Int(f"dest_{d}") for d in range(1, n_days + 1)]
    EndCity = [Int(f"end_{d}") for d in range(1, n_days + 1)]
    Flight = [Bool(f"flight_{d}") for d in range(1, n_days + 1)]

    # Presence[city][day] -> Bool
    Presence = {
        city: [Bool(f"present_{city}_{d}") for d in range(1, n_days + 1)]
        for city in (RIGA, AMS, MYK)
    }

    s = Solver()

    # Domains
    for d in range(n_days):
        s.add(And(StartCity[d] >= 0, StartCity[d] <= 2))
        s.add(And(DestCity[d] >= 0, DestCity[d] <= 2))
        s.add(And(EndCity[d] >= 0, EndCity[d] <= 2))

    # EndCity definition and valid flights
    for d in range(n_days):
        s.add(EndCity[d] == If(Flight[d], DestCity[d], StartCity[d]))
        # If a flight occurs, it must be between distinct cities and be a direct route
        s.add(Implies(Flight[d], DestCity[d] != StartCity[d]))
        s.add(Implies(
            Flight[d],
            Or(*[And(StartCity[d] == a, DestCity[d] == b) for (a, b) in direct_flights])
        ))

    # Continuity: next day's start is previous day's end
    for d in range(1, n_days):
        s.add(StartCity[d] == EndCity[d - 1])

    # Presence constraints per city/day
    for city in (RIGA, AMS, MYK):
        for d in range(n_days):
            s.add(Presence[city][d] ==
                  Or(StartCity[d] == city, And(Flight[d], DestCity[d] == city)))

    # Total days in each city
    for city, days_required in required_days.items():
        s.add(Sum([If(Presence[city][d], 1, 0) for d in range(n_days)]) == days_required)

    # "Visit relatives in Riga between day 1 and day 2" => be in Riga on Day 1 and Day 2
    s.add(Presence[RIGA][0])  # Day 1
    s.add(Presence[RIGA][1])  # Day 2

    # The total "city-days" equals n_days + number_of_flights, so with 2+2+5=9, we must have 2 flights
    s.add(Sum([If(Flight[d], 1, 0) for d in range(n_days)]) == 2)

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}, ensure_ascii=False))
        return

    m = s.model()

    # Extract end-of-day city per day
    end_cities = [m[EndCity[d]].as_long() for d in range(n_days)]

    # Build itinerary by merging contiguous days with same end city
    itinerary = []
    start_day = 1
    current_city = end_cities[0]
    for day in range(2, n_days + 1):
        if end_cities[day - 1] != current_city:
            itinerary.append({
                "day_range": f"Day {start_day}-{day - 1}",
                "place": city_names[current_city]
            })
            start_day = day
            current_city = end_cities[day - 1]
    # Append last segment
    itinerary.append({
        "day_range": f"Day {start_day}-{n_days}",
        "place": city_names[current_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()