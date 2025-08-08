from z3 import Solver, IntVector, sat

def main():
    city_data = {
        'London': {'min_days': 5},
        'Split': {'min_days': 3},
        'Oslo': {'min_days': 2},
        'Porto': {'min_days': 4}
    }
    itinerary_order = ['London', 'Split', 'Oslo', 'Porto']
    n = len(itinerary_order)
    
    min_days = [city_data[city]['min_days'] for city in itinerary_order]
    
    s = Solver()
    start_day = IntVector('start_day', n)
    end_day = IntVector('end_day', n)
    
    # First city starts on Day 1
    s.add(start_day[0] == 1)
    # Last city ends on Day 16
    s.add(end_day[n-1] == 16)
    
    # Continuity: next city starts on same day previous ends (travel included in stay)
    for i in range(n-1):
        s.add(start_day[i+1] == end_day[i])
    
    # Minimum stay and valid day ranges
    for i in range(n):
        s.add(end_day[i] - start_day[i] + 1 >= min_days[i])
        s.add(start_day[i] <= end_day[i])
        s.add(start_day[i] >= 1)
        s.add(end_day[i] <= 16)
    
    # Total days must sum to 16
    total_days = sum(end_day[i] - start_day[i] + 1 for i in range(n))
    s.add(total_days == 16)
    
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