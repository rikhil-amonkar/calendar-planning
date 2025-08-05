from z3 import *

def main():
    s = Solver()
    n_days = 16
    city = [Int(f'city_{i}') for i in range(n_days)]
    
    city_names = {
        0: 'London',
        1: 'Hamburg',
        2: 'Dublin',
        3: 'Helsinki',
        4: 'Reykjavik',
        5: 'Mykonos'
    }
    
    for i in range(n_days):
        s.add(city[i] >= 0, city[i] <= 5)
    
    s.add(city[0] == 0)
    s.add(city[15] == 0)
    
    allowed_flights = [
        (0,1), (0,2), (0,4), (0,5),
        (1,0), (1,2), (1,3),
        (2,0), (2,1), (2,4),
        (3,1), (3,4),
        (4,0), (4,2), (4,3), (4,5),
        (5,0), (5,4)
    ]
    
    for i in range(n_days - 1):
        c1 = city[i]
        c2 = city[i+1]
        s.add(Or(c1 == c2, Or([And(c1 == a, c2 == b) for (a, b) in allowed_flights])))
    
    for i in range(n_days - 3):
        s.add(Not(And(city[i] == city[i+1], city[i+1] == city[i+2], city[i+2] == city[i+3])))
    
    for c in range(6):
        s.add(Or([city[i] == c for i in range(n_days)]))
    
    # Block previous invalid solutions
    prev_solution1 = [0, 0, 2, 4, 5, 0, 1, 3, 4, 5, 0, 1, 3, 4, 5, 0]
    prev_solution2 = [0, 2, 4, 5, 0, 1, 3, 4, 5, 0, 1, 3, 4, 5, 4, 0]
    s.add(Or([city[i] != prev_solution1[i] for i in range(n_days)]))
    s.add(Or([city[i] != prev_solution2[i] for i in range(n_days)]))
    
    if s.check() == sat:
        m = s.model()
        assignment = [m.evaluate(city[i]).as_long() for i in range(n_days)]
        
        itinerary = []
        start_idx = 0
        current_city = assignment[0]
        for i in range(1, n_days):
            if assignment[i] != current_city:
                start_day = start_idx + 1
                end_day = i
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary.append({
                    'day_range': day_range,
                    'place': city_names[current_city]
                })
                start_idx = i
                current_city = assignment[i]
        
        # Add last segment
        start_day = start_idx + 1
        end_day = n_days
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        itinerary.append({
            'day_range': day_range,
            'place': city_names[current_city]
        })
        
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()