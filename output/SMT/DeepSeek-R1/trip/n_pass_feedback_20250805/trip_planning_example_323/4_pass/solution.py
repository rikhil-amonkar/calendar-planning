from z3 import Solver, Int, sat

def main():
    city_data = [
        {'name': 'London', 'min_days': 5},
        {'name': 'Split', 'min_days': 3},
        {'name': 'Oslo', 'min_days': 2},
        {'name': 'Porto', 'min_days': 4}
    ]
    n = len(city_data)
    
    # Create start and end day variables for each city
    start_day = [Int(f'start_{i}') for i in range(n)]
    end_day = [Int(f'end_{i}') for i in range(n)]
    
    s = Solver()
    
    # First city starts on Day 1
    s.add(start_day[0] == 1)
    # Last city ends on Day 16
    s.add(end_day[n-1] == 16)
    
    # Continuity constraints (no gaps)
    for i in range(n-1):
        s.add(end_day[i] + 1 == start_day[i+1])
    
    # Minimum stay constraints
    for i in range(n):
        min_days = city_data[i]['min_days']
        s.add(end_day[i] - start_day[i] + 1 >= min_days)
        s.add(start_day[i] >= 1)
        s.add(end_day[i] <= 16)
        s.add(start_day[i] <= end_day[i])
    
    # Total days must sum to exactly 16
    total_days = sum(end_day[i] - start_day[i] + 1 for i in range(n))
    s.add(total_days == 16)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            s_val = m[start_day[i]].as_long()
            e_val = m[end_day[i]].as_long()
            city = city_data[i]['name']
            if s_val == e_val:
                day_range = f"Day {s_val}"
            else:
                day_range = f"Day {s_val}-{e_val}"
            itinerary.append({'day_range': day_range, 'place': city})
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()