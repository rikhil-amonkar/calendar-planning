from z3 import *

def main():
    s = Solver()
    days = list(range(1, 17))
    cities = ['Bucharest', 'Lyon', 'Porto']
    # Create variables: for each day and city, a boolean
    vars = {}
    for d in days:
        for city in cities:
            vars[(d, city)] = Bool(f"day{d}_{city}")
    
    # Constraints for each day
    for d in days:
        B = vars.get((d, 'Bucharest'))
        L = vars.get((d, 'Lyon'))
        P = vars.get((d, 'Porto'))
        states = [
            And(B, Not(L), Not(P)),
            And(L, Not(B), Not(P)),
            And(P, Not(B), Not(L)),
            And(B, L, Not(P)),
            And(L, P, Not(B))
        ]
        s.add(Or(states))
    
    # Total days per city
    total_days = { 
        'Bucharest': 7,
        'Lyon': 7,
        'Porto': 4 
    }
    for city in cities:
        total = 0
        for d in days:
            total += If(vars[(d, city)], 1, 0)
        s.add(total == total_days[city])
    
    # Wedding constraint: at least one day in Bucharest between 1 and 7
    s.add(Or([vars[(d, 'Bucharest')] for d in range(1, 8)]))
    
    # Flight days: days with two cities, must be connected (B-L or L-P)
    flight_days = []
    for d in days:
        B = vars.get((d, 'Bucharest'))
        L = vars.get((d, 'Lyon'))
        P = vars.get((d, 'Porto'))
        flight_days.append(If(Or(And(B, L, Not(P)), And(L, P, Not(B))), 1, 0))
    s.add(Sum(flight_days) == 2)
    
    # Connectivity: consecutive days share at least one city
    for d in range(1, 16):
        B_curr = vars.get((d, 'Bucharest'))
        L_curr = vars.get((d, 'Lyon'))
        P_curr = vars.get((d, 'Porto'))
        B_next = vars.get((d+1, 'Bucharest'))
        L_next = vars.get((d+1, 'Lyon'))
        P_next = vars.get((d+1, 'Porto'))
        s.add(Or(
            And(B_curr, B_next),
            And(L_curr, L_next),
            And(P_curr, P_next)
        ))
    
    # Solve
    if s.check() == sat:
        model = s.model()
        in_city = {}
        for d in days:
            for city in cities:
                in_city[(d, city)] = model.evaluate(vars[(d, city)])
        
        # Find flight days
        flight_days_list = []
        for d in days:
            count = 0
            for city in cities:
                if in_city[(d, city)]:
                    count += 1
            if count == 2:
                flight_days_list.append(d)
        
        # Determine departure and arrival for each flight day
        flight_events_dict = {}
        for d in flight_days_list:
            if d == 1:
                continue
            prev_cities = [city for city in cities if in_city[(d-1, city)]]
            curr_cities = [city for city in cities if in_city[(d, city)]]
            if len(prev_cities) == 1:
                dep_city = prev_cities[0]
                arr_city = [c for c in curr_cities if c != dep_city][0]
            else:
                common = set(prev_cities) & set(curr_cities)
                if common:
                    dep_city = common.pop()
                    arr_city = [c for c in curr_cities if c != dep_city][0]
                else:
                    dep_city = curr_cities[0]
                    arr_city = curr_cities[1]
            flight_events_dict[d] = (dep_city, arr_city)
        
        # Compute contiguous blocks per city
        blocks = {city: [] for city in cities}
        for city in cities:
            days_list = sorted([d for d in days if in_city[(d, city)]])
            if not days_list:
                continue
            start = days_list[0]
            end = days_list[0]
            for i in range(1, len(days_list)):
                if days_list[i] == end + 1:
                    end = days_list[i]
                else:
                    blocks[city].append((start, end))
                    start = days_list[i]
                    end = days_list[i]
            blocks[city].append((start, end))
        
        # Starts for quick lookup
        starts = {city: [block[0] for block in blocks[city]] for city in cities}
        
        # Build itinerary
        itinerary = []
        for d in days:
            if d in flight_events_dict:
                dep_city, arr_city = flight_events_dict[d]
                itinerary.append({"day_range": f"Day {d}", "place": dep_city})
                itinerary.append({"day_range": f"Day {d}", "place": arr_city})
            for city in cities:
                if d in starts[city]:
                    block = [b for b in blocks[city] if b[0] == d][0]
                    s_day, e_day = block
                    if s_day == e_day:
                        dr = f"Day {s_day}"
                    else:
                        dr = f"Day {s_day}-{e_day}"
                    itinerary.append({"day_range": dr, "place": city})
        
        # Output
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()