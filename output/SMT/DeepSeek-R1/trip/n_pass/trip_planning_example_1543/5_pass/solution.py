from z3 import *

def main():
    cities = ["Prague", "Warsaw", "Dublin", "Athens", "Vilnius", "Porto", "London", "Seville", "Lisbon", "Dubrovnik"]
    durations = [3, 4, 3, 3, 4, 5, 3, 2, 5, 3]
    
    flights = [
        (1, 4), (0, 3), (6, 8), (8, 5), (0, 8), (6, 2), (3, 4), (3, 2), (0, 6), (6, 1),
        (2, 7), (7, 5), (8, 3), (2, 5), (3, 1), (8, 1), (5, 1), (0, 1), (0, 2), (3, 9),
        (8, 2), (9, 2), (8, 7), (6, 3)
    ]
    
    directed_flights = set()
    for (i, j) in flights:
        directed_flights.add((i, j))
        directed_flights.add((j, i))
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(10)]
    for i in range(10):
        s.add(order[i] >= 0, order[i] < 10)
    s.add(Distinct(order))
    
    dur_arr = Array('dur_arr', IntSort(), IntSort())
    for i in range(10):
        s.add(dur_arr[i] == durations[i])
    
    start_day = [Int(f'start_day_{i}') for i in range(10)]
    s.add(start_day[0] == 1)
    
    for k in range(1, 10):
        s.add(start_day[k] == start_day[k-1] + dur_arr[order[k-1]] - 1)
    
    s.add(start_day[9] + dur_arr[order[9]] - 1 == 26)
    
    flight_ok = Function('flight_ok', IntSort(), IntSort(), BoolSort())
    for a in range(10):
        for b in range(10):
            if (a, b) in directed_flights:
                s.add(flight_ok(a, b))
            else:
                s.add(Not(flight_ok(a, b)))
    
    for k in range(9):
        s.add(flight_ok(order[k], order[k+1]))
    
    event_constraints = [
        (0, 3),   # Prague on day 3
        (6, 5),   # London on day 5
        (5, 16),  # Porto on day 16
        (8, 9),   # Lisbon on day 9
        (1, 20)   # Warsaw on day 20
    ]
    
    for city_index, event_day in event_constraints:
        for k in range(10):
            s.add(If(order[k] == city_index,
                     And(start_day[k] <= event_day, event_day <= start_day[k] + dur_arr[order[k]] - 1),
                     True))
    
    s.add(order[9] == 9)  # Dubrovnik must be the last city
    s.add(Or(order[8] == 3, order[8] == 2))  # The city before Dubrovnik must be Athens (3) or Dublin (2)
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[k]).as_long() for k in range(10)]
        start_day_vals = [m.evaluate(start_day[k]).as_long() for k in range(10)]
        
        stay_list = []
        for k in range(10):
            city_index = order_vals[k]
            start = start_day_vals[k]
            end = start + durations[city_index] - 1
            stay_list.append((cities[city_index], start, end))
        
        itinerary = []
        for (city, start, end) in stay_list:
            itinerary.append({
                'day_range': f'Day {start}-{end}',
                'place': city
            })
        
        result = {"itinerary": itinerary}
        print("Plan found:", result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()