from z3 import *

def main():
    # Define city indices and stay durations
    cities = ['Salzburg', 'Venice', 'Bucharest', 'Brussels', 'Hamburg', 'Copenhagen', 'Nice', 'Zurich', 'Naples']
    days_arr = [2, 5, 4, 2, 4, 4, 3, 5, 4]  # Corresponding to cities
    mapping = {city: idx for idx, city in enumerate(cities)}
    
    # Flight connections (undirected, stored as directed both ways)
    connection_list = [
        "Zurich and Brussels", "Bucharest and Copenhagen", "Venice and Brussels",
        "Nice and Zurich", "Hamburg and Nice", "Zurich and Naples",
        "Hamburg and Bucharest", "Zurich and Copenhagen", "Bucharest and Brussels",
        "Hamburg and Brussels", "Venice and Naples", "Venice and Copenhagen",
        "Bucharest and Naples", "Hamburg and Copenhagen", "Venice and Zurich",
        "Nice and Brussels", "Hamburg and Venice", "Copenhagen and Naples",
        "Nice and Naples", "Hamburg and Zurich", "Salzburg and Hamburg",
        "Zurich and Bucharest", "Brussels and Naples", "Copenhagen and Brussels",
        "Venice and Nice", "Nice and Copenhagen"
    ]
    allowed_edges = set()
    for conn in connection_list:
        parts = conn.split(' and ')
        city1 = parts[0].strip()
        city2 = parts[1].strip()
        idx1 = mapping[city1]
        idx2 = mapping[city2]
        allowed_edges.add((idx1, idx2))
        allowed_edges.add((idx2, idx1))
    
    # Z3 solver setup
    s = Solver()
    
    # Order of cities (permutation)
    order = [Int(f'order_{i}') for i in range(9)]
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    s.add(Distinct(order))
    
    # Arrival days for each position in the sequence
    arrival_pos = [Int(f'arrival_pos_{i}') for i in range(9)]
    s.add(arrival_pos[0] == 1)
    for i in range(1, 9):
        prev_duration = days_arr[order[i-1]]
        s.add(arrival_pos[i] == arrival_pos[i-1] + (prev_duration - 1))
    
    # Flight constraints between consecutive cities
    for i in range(8):
        constraints = []
        for (a, b) in allowed_edges:
            constraints.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(constraints))
    
    # Event constraints
    arrival_brussels = Int('arrival_brussels')
    brussels_sum = Sum([If(order[i] == 3, arrival_pos[i], 0) for i in range(9)])
    s.add(arrival_brussels == brussels_sum)
    s.add(arrival_brussels >= 20, arrival_brussels <= 22)
    
    arrival_copenhagen = Int('arrival_copenhagen')
    copenhagen_sum = Sum([If(order[i] == 5, arrival_pos[i], 0) for i in range(9)])
    s.add(arrival_copenhagen == copenhagen_sum)
    s.add(arrival_copenhagen >= 15, arrival_copenhagen <= 21)
    
    arrival_nice = Int('arrival_nice')
    nice_sum = Sum([If(order[i] == 6, arrival_pos[i], 0) for i in range(9)])
    s.add(arrival_nice == nice_sum)
    s.add(arrival_nice >= 7, arrival_nice <= 11)
    
    arrival_naples = Int('arrival_naples')
    naples_sum = Sum([If(order[i] == 8, arrival_pos[i], 0) for i in range(9)])
    s.add(arrival_naples == naples_sum)
    s.add(arrival_naples >= 19, arrival_naples <= 25)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(9)]
        arrival_vals = [m.evaluate(arrival_pos[i]).as_long() for i in range(9)]
        
        itinerary = []
        for i in range(9):
            city_idx = order_vals[i]
            city_name = cities[city_idx]
            a = arrival_vals[i]
            duration = days_arr[city_idx]
            d = a + duration - 1
            itinerary.append({"day_range": f"Day {a}-{d}", "place": city_name})
            if i < 8:
                next_city_idx = order_vals[i+1]
                next_city_name = cities[next_city_idx]
                itinerary.append({"day_range": f"Day {d}", "place": city_name})
                itinerary.append({"day_range": f"Day {d}", "place": next_city_name})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()