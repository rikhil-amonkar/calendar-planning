from z3 import *

def main():
    cities = ['Santorini', 'Valencia', 'Madrid', 'Seville', 'Bucharest', 'Vienna', 'Riga', 'Tallinn', 'Krakow', 'Frankfurt']
    days = [3, 4, 2, 2, 3, 4, 4, 5, 5, 4]
    
    edges = [
        (5, 4), (0, 2), (3, 1), (5, 3), (2, 1), (4, 6), (1, 4), (0, 4), 
        (5, 1), (5, 2), (1, 8), (1, 9), (8, 9), (6, 7), (5, 8), (5, 9), 
        (2, 3), (0, 5), (5, 6), (9, 7), (9, 4), (2, 4), (9, 6), (2, 9)
    ]
    
    direct_flights = set()
    for a, b in edges:
        direct_flights.add((a, b))
        direct_flights.add((b, a))
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(10)]
    arrivals = [Int(f'arrival_{i}') for i in range(10)]
    
    s.add(Distinct(order))
    for i in range(10):
        s.add(And(order[i] >= 0, order[i] < 10))
        s.add(And(arrivals[i] >= 1, arrivals[i] <= 27 - (days[i] - 1)))
    
    s.add(arrivals[2] == 6)
    s.add(arrivals[8] == 11)
    s.add(arrivals[6] == 20)
    s.add(arrivals[7] == 23)
    s.add(arrivals[5] <= 6)
    
    s.add(arrivals[order[0]] == 1)
    last_city = order[9]
    s.add(arrivals[last_city] + (days[last_city] - 1) == 27)
    
    for i in range(9):
        current_city = order[i]
        next_city = order[i+1]
        s.add(arrivals[next_city] == arrivals[current_city] + (days[current_city] - 1))
    
    for i in range(9):
        constraints = []
        for a, b in direct_flights:
            constraints.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(constraints))
    
    if s.check() == sat:
        m = s.model()
        order_list = [m.evaluate(order[i]).as_long() for i in range(10)]
        arrivals_list = [m.evaluate(arrivals[i]).as_long() for i in range(10)]
        departures_list = [arrivals_list[i] + (days[i] - 1) for i in range(10)]
        
        itinerary = []
        for i in range(10):
            city_index = order_list[i]
            a = arrivals_list[city_index]
            d = departures_list[city_index]
            city_name = cities[city_index]
            itinerary.append({"day_range": f"Day {a}-{d}", "place": city_name})
            if i < 9:
                itinerary.append({"day_range": f"Day {d}", "place": city_name})
                next_city_index = order_list[i+1]
                next_city_name = cities[next_city_index]
                a_next = arrivals_list[next_city_index]
                itinerary.append({"day_range": f"Day {a_next}", "place": next_city_name})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()