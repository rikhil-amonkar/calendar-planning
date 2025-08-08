from z3 import Solver, Bool, Sum, If, Or, And, Implies, Not, sat
import json

def main():
    cities = ["Hamburg", "Dublin", "Reykjavik", "London", "Helsinki", "Mykonos"]
    days = list(range(1, 17))  # Days 1 to 16
    in_city = {c: {d: Bool(f'in_{c}_{d}') for d in days} for c in cities}

    s = Solver()

    # Total days per city
    s.add(Sum([If(in_city["Hamburg"][d], 1, 0) for d in days]) == 2)
    s.add(Sum([If(in_city["Dublin"][d], 1, 0) for d in days]) == 5)
    s.add(Sum([If(in_city["Reykjavik"][d], 1, 0) for d in days]) == 2)
    s.add(Sum([If(in_city["London"][d], 1, 0) for d in days]) == 5)
    s.add(Sum([If(in_city["Helsinki"][d], 1, 0) for d in days]) == 4)
    s.add(Sum([If(in_city["Mykonos"][d], 1, 0) for d in days]) == 3)

    # Each day: at least one city, at most two cities
    for d in days:
        s.add(Or([in_city[c][d] for c in cities]))
        s.add(Sum([If(in_city[c][d], 1, 0) for c in cities]) <= 2)

    # Consecutive days must share at least one city
    for d in range(1, 16):
        s.add(Or([And(in_city[c][d], in_city[c][d+1]) for c in cities]))

    # Define direct flights
    flights = [
        ("Dublin", "London"),
        ("Hamburg", "Dublin"),
        ("Helsinki", "Reykjavik"),
        ("Hamburg", "London"),
        ("Dublin", "Helsinki"),
        ("Reykjavik", "London"),
        ("London", "Mykonos"),
        ("Dublin", "Reykjavik"),
        ("Hamburg", "Helsinki"),
        ("Helsinki", "London")
    ]
    flight_set = set()
    for a, b in flights:
        if a < b:
            flight_set.add((a, b))
        else:
            flight_set.add((b, a))

    # Flight constraints: if two cities are present on the same day, they must be connected
    for d in days:
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                edge = (c1, c2) if c1 < c2 else (c2, c1)
                if edge not in flight_set:
                    s.add(Implies(And(in_city[c1][d], in_city[c2][d]), False))

    # Fixed events
    s.add(in_city["Hamburg"][1] == True)
    s.add(in_city["Hamburg"][2] == True)
    for d in [2,3,4,5,6]:
        s.add(in_city["Dublin"][d] == True)
    s.add(in_city["Reykjavik"][9] == True)
    s.add(in_city["Reykjavik"][10] == True)

    # Day 1: only in Hamburg (start)
    for c in cities:
        if c != "Hamburg":
            s.add(in_city[c][1] == False)

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for d in days:
            for c in cities:
                if m.evaluate(in_city[c][d]):
                    itinerary_list.append({"day": d, "city": c})
        result = {'itinerary': itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()