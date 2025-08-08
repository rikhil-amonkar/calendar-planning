from z3 import Solver, IntVector, sat

def main():
    city_data = {
        'London': {'min_days': 5, 'max_days': None},
        'Split': {'min_days': 3, 'max_days': None},
        'Oslo': {'min_days': 2, 'max_days': None},
        'Porto': {'min_days': 4, 'max_days': None}
    }
    itinerary_order = ['London', 'Split', 'Oslo', 'Porto']
    n = len(itinerary_order)
    
    min_days = [city_data[city]['min_days'] for city in itinerary_order]
    
    s = Solver()
    start_day = IntVector('start_day', n)
    end_day = IntVector('end_day', n)
    
    s.add(start_day[0] == 1)
    s.add(end_day[n-1] == 16)
    
    for i in range(n-1):
        s.add(end_day[i] + 1 == start_day[i+1])
    
    for i in range(n):
        s.add(start_day[i] >= 1)
        s.add(end_day[i] <= 16)
        s.add(start_day[i] <= end_day[i])
        s.add(end_day[i] - start_day[i] + 1 >= min_days[i])
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            s_val = m[start_day[i]].as_long()
            e_val = m[end_day[i]].as_long()
            if s_val == e_val:
                day_range = f"Day {s_val}"
            else:
                day_range = f"Day {s_val}-{e_val}"
            itinerary.append({'day_range': day_range, 'place': itinerary_order[i]})
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()