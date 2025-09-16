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
    
    dur = Array('dur', IntSort(), IntSort())
    for i in range(10):
        s.add(dur[i] == durations[i])
    
    start_day = [Int(f'start_day_{i}') for i in range(10)]
    s.add(start_day[0] == 1)
    
    for k in range(1, 10):
        s.add(start_day[k] == start_day[k-1] + dur[order[k-1]] - 1)
    
    s.add(start_day[9] + dur[order[9]] - 1 == 26)
    
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
        (0, lambda x: x <= 3),
        (1, lambda x: And(x >= 17, x <= 23)),
        (5, lambda x: And(x >= 12, x <= 20)),
        (6, lambda x: x <= 5),
        (8, lambda x: x <= 9)
    ]
    
    for city_index, constraint in event_constraints:
        for k in range(10):
            s.add(If(order[k] == city_index, constraint(start_day[k]), True))
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[k]).as_long() for k in range(10)]
        start_day_vals = [m.evaluate(start_day[k]).as_long() for k in range(10)]
        
        city_stays = {}
        for k in range(10):
            city_index = order_vals[k]
            start = start_day_vals[k]
            end = start + durations[city_index] - 1
            city_stays[city_index] = (start, end)
        
        itinerary = []
        for day in range(1, 27):
            places = []
            for city_index in range(10):
                start, end = city_stays[city_index]
                if start <= day <= end:
                    places.append(cities[city_index])
            itinerary.append({"day": day, "place": places})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()