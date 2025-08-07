import multiprocessing
import json
from z3 import Solver, Bool, Sum, If, Or, And, Not

def solve_itinerary():
    cities = ["Hamburg", "Dublin", "Reykjavik", "London", "Helsinki", "Mykonos"]
    days = list(range(1, 17))
    in_city = {c: {d: Bool(f'in_{c}_{d}') for d in days} for c in cities}

    s = Solver()

    # Fixed events: Hamburg (days 1-2), Dublin (days 2-6), Reykjavik (days 9-10)
    s.add(in_city["Hamburg"][1] == True)
    s.add(in_city["Hamburg"][2] == True)
    s.add(in_city["Dublin"][2] == True, in_city["Dublin"][3] == True, 
          in_city["Dublin"][4] == True, in_city["Dublin"][5] == True, 
          in_city["Dublin"][6] == True)
    s.add(in_city["Reykjavik"][9] == True, in_city["Reykjavik"][10] == True)

    # Constraints for day 1 (only Hamburg) and day 2 (Hamburg and Dublin)
    for city in ["Dublin", "Reykjavik", "London", "Helsinki", "Mykonos"]:
        s.add(in_city[city][1] == False)
    for city in ["Reykjavik", "London", "Helsinki", "Mykonos"]:
        s.add(in_city[city][2] == False)

    # Total days per city
    s.add(Sum([If(in_city["London"][d], 1, 0) for d in days]) == 5)
    s.add(Sum([If(in_city["Helsinki"][d], 1, 0) for d in days]) == 4)
    s.add(Sum([If(in_city["Mykonos"][d], 1, 0) for d in days]) == 3)

    # Daily constraints: at least one city, at most two cities
    for d in days:
        s.add(Or([in_city[c][d] for c in cities]))
        s.add(Sum([If(in_city[c][d], 1, 0) for c in cities]) <= 2)

    # Consecutive days must share at least one city
    for d in range(1, 16):
        s.add(Or([And(in_city[c][d], in_city[c][d+1]) for c in cities]))

    # Direct flight connections
    flights = [("Dublin", "London"), ("Hamburg", "Dublin"), 
               ("Helsinki", "Reykjavik"), ("Hamburg", "London"),
               ("Dublin", "Helsinki"), ("Reykjavik", "London"),
               ("London", "Mykonos"), ("Dublin", "Reykjavik"),
               ("Hamburg", "Helsinki"), ("Helsinki", "London")]
    allowed_pairs = {(a, b) if a < b else (b, a) for a, b in flights}
    for d in days:
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1, c2 = cities[i], cities[j]
                if (c1, c2) not in allowed_pairs:
                    s.add(Not(And(in_city[c1][d], in_city[c2][d])))

    # Solve and return itinerary
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in days:
            for c in cities:
                if m.evaluate(in_city[c][d]):
                    itinerary.append({"day": d, "city": c})
        return json.dumps({"itinerary": itinerary})
    else:
        return json.dumps({"error": "No solution found"})

if __name__ == '__main__':
    queue = multiprocessing.Queue()
    process = multiprocessing.Process(target=lambda q: q.put(solve_itinerary()), args=(queue,))
    process.start()
    process.join()
    result = queue.get() if not queue.empty() else json.dumps({"error": "Solver failed"})
    print(result)