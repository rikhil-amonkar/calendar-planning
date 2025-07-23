import z3
import json

def main():
    cities = {0: 'Riga', 1: 'Amsterdam', 2: 'Mykonos'}
    s = 0  # Starting city is Riga
    d = [z3.Int(f'd{i}') for i in range(7)]  # Ending cities for days 1 to 7

    valid_pairs = [(0, 1), (1, 0), (1, 2), (2, 1)]
    solver = z3.Solver()

    for i in range(7):
        solver.add(d[i] >= 0, d[i] <= 2)

    # Flight constraint for day 1: if not staying in Riga, must fly to Amsterdam
    solver.add(z3.Implies(d[0] != 0, d[0] == 1))

    # Flight constraints for consecutive days
    for j in range(6):
        solver.add(z3.Implies(d[j] != d[j+1],
            z3.Or(
                z3.And(d[j] == 0, d[j+1] == 1),
                z3.And(d[j] == 1, d[j+1] == 0),
                z3.And(d[j] == 1, d[j+1] == 2),
                z3.And(d[j] == 2, d[j+1] == 1)
            )))
    
    # Total flights must be 2
    flight_days = [z3.If(s != d[0], 1, 0)]
    for j in range(6):
        flight_days.append(z3.If(d[j] != d[j+1], 1, 0))
    total_flights = sum(flight_days)
    solver.add(total_flights == 2)

    # Days in Riga (must be 2, including day 1 and 2)
    count_R = 1  # Day 1 is always in Riga (s=0)
    for j in range(6):
        cond = z3.Or(d[j] == 0, d[j+1] == 0)
        count_R += z3.If(cond, 1, 0)
    solver.add(count_R == 2)

    # Days in Amsterdam (must be 2)
    count_A = z3.If(z3.Or(s == 1, d[0] == 1), 1, 0)
    for j in range(6):
        cond = z3.Or(d[j] == 1, d[j+1] == 1)
        count_A += z3.If(cond, 1, 0)
    solver.add(count_A == 2)

    # Days in Mykonos (must be 5)
    count_M = z3.If(z3.Or(s == 2, d[0] == 2), 1, 0)
    for j in range(6):
        cond = z3.Or(d[j] == 2, d[j+1] == 2)
        count_M += z3.If(cond, 1, 0)
    solver.add(count_M == 5)

    if solver.check() == z3.sat:
        model = solver.model()
        d_vals = [model.eval(di).as_long() for di in d]

        presence = {0: [], 1: [], 2: []}
        presence[0].append(1)  # Day 1 in Riga

        if d_vals[0] == 1:
            presence[1].append(1)
        if d_vals[0] == 2:
            presence[2].append(1)

        for day_index in range(2, 8):
            idx_prev = day_index - 2
            idx_curr = day_index - 1
            prev_city = d_vals[idx_prev]
            curr_city = d_vals[idx_curr]
            for city in [0, 1, 2]:
                if prev_city == city or curr_city == city:
                    presence[city].append(day_index)
        
        itinerary_ranges = []
        for city, days_list in presence.items():
            if days_list:
                min_day = min(days_list)
                max_day = max(days_list)
                itinerary_ranges.append((min_day, max_day, cities[city]))
        
        itinerary_ranges.sort(key=lambda x: x[0])
        itinerary = [
            {"day_range": f"Day {start}-{end}", "place": place}
            for start, end, place in itinerary_ranges
        ]
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()