from z3 import Solver, Bool, Sum, If, Or, And, Not, Implies, sat
import json

def main():
    cities = ["Hamburg", "Dublin", "Reykjavik", "London", "Helsinki", "Mykonos"]
    days = list(range(1, 17))  # Days 1 to 16
    in_city = {c: {d: Bool(f'in_{c}_{d}') for d in days} for c in cities}

    s = Solver()

    # Fixed events and total days per city
    # Hamburg: days 1 and 2
    s.add(in_city["Hamburg"][1] == True)
    s.add(in_city["Hamburg"][2] == True)
    for d in range(3, 17):
        s.add(in_city["Hamburg"][d] == False)

    # Dublin: days 2,3,4,5,6
    for d in [2,3,4,5,6]:
        s.add(in_city["Dublin"][d] == True)
    for d in [1] + list(range(7,17)):
        s.add(in_city["Dublin"][d] == False)

    # Reykjavik: days 9 and 10
    s.add(in_city["Reykjavik"][9] == True)
    s.add(in_city["Reykjavik"][10] == True)
    for d in list(range(1,9)) + list(range(11,17)):
        s.add(in_city["Reykjavik"][d] == False)

    # Day 1: only Hamburg
    for city in ['Dublin', 'Reykjavik', 'London', 'Helsinki', 'Mykonos']:
        s.add(in_city[city][1] == False)

    # Day 2: only Hamburg and Dublin
    for city in ['Reykjavik', 'London', 'Helsinki', 'Mykonos']:
        s.add(in_city[city][2] == False)

    # Total days for the remaining cities
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

    # Define direct flights as allowed pairs
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
    allowed_pairs = set()
    for a, b in flights:
        if a < b:
            pair = (a, b)
        else:
            pair = (b, a)
        allowed_pairs.add(pair)

    # For each day, if two distinct cities are both present, they must be connected
    for d in days:
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                if (c1, c2) not in allowed_pairs and (c2, c1) not in allowed_pairs:
                    s.add(Not(And(in_city[c1][d], in_city[c2][d])))

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