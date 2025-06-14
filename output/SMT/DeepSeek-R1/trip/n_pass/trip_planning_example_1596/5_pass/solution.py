from z3 import *

def main():
    s = Solver()

    cities_list = ['Bucharest', 'Krakow', 'Munich', 'Barcelona', 'Warsaw', 'Budapest', 'Stockholm', 'Riga', 'Edinburgh', 'Vienna']
    
    durations_dict = {
        'Bucharest': 2,
        'Krakow': 4,
        'Munich': 3,
        'Barcelona': 5,
        'Warsaw': 5,
        'Budapest': 5,
        'Stockholm': 2,
        'Riga': 5,
        'Edinburgh': 5,
        'Vienna': 5
    }
    
    A = {city: Int(f'A_{city}') for city in cities_list}
    D = {city: A[city] + durations_dict[city] - 1 for city in cities_list}
    
    O = {city: Int(f'O_{city}') for city in cities_list}
    
    s.add(Distinct([O[city] for city in cities_list]))
    for city in cities_list:
        s.add(O[city] >= 0)
        s.add(O[city] <= 9)
    
    s.add(A['Munich'] == 18)
    s.add(A['Warsaw'] == 25)
    s.add(A['Budapest'] == 9)
    s.add(A['Stockholm'] == 17)
    s.add(A['Edinburgh'] >= 1, A['Edinburgh'] <= 5)
    
    s.add(Or([And(O[city] == 0, A[city] == 1) for city in cities_list]))
    s.add(Or([And(O[city] == 9, D[city] == 32) for city in cities_list]))
    
    flight_list_str = [
        "Budapest and Munich", 
        "Bucharest and Riga", 
        "Munich and Krakow",
        "Munich and Warsaw", 
        "Munich and Bucharest", 
        "Edinburgh and Stockholm", 
        "Barcelona and Warsaw", 
        "Edinburgh and Krakow", 
        "Barcelona and Munich", 
        "Stockholm and Krakow", 
        "Budapest and Vienna", 
        "Barcelona and Stockholm", 
        "Stockholm and Munich", 
        "Edinburgh and Budapest", 
        "Barcelona and Riga", 
        "Edinburgh and Barcelona", 
        "Stockholm and Riga", 
        "Barcelona and Bucharest", 
        "Bucharest and Warsaw", 
        "Vienna and Krakow", 
        "Edinburgh and Munich", 
        "Barcelona and Bucharest",
        "Edinburgh and Riga", 
        "Vienna and Stockholm", 
        "Warsaw and Krakow", 
        "Barcelona and Krakow", 
        "from Riga to Munich", 
        "Vienna and Bucharest", 
        "Budapest and Warsaw", 
        "Vienna and Warsaw", 
        "Barcelona and Vienna", 
        "Budapest and Bucharest", 
        "Vienna and Munich", 
        "Riga and Warsaw", 
        "Stockholm and Riga", 
        "Stockholm and Warsaw"
    ]
    
    # Correct typos: replace "Munich" with "Munich"
    corrected_flight_list = [s.replace("Munich", "Munich") for s in flight_list_str]
    
    undirected_flight_set = set()
    for s_str in corrected_flight_list:
        if " and " in s_str:
            parts = s_str.split(" and ")
            if len(parts) == 2:
                c1 = parts[0].strip()
                c2 = parts[1].strip()
                if c1 in cities_list and c2 in cities_list:
                    key = (min(c1, c2), max(c1, c2))
                    undirected_flight_set.add(key)
        elif " to " in s_str:
            parts = s_str.split(" to ")
            if len(parts) >= 2:
                c1_part = parts[0]
                if c1_part.startswith("from "):
                    c1 = c1_part[5:].strip()
                else:
                    c1 = c1_part.strip()
                c2 = parts[1].strip()
                if c1 in cities_list and c2 in cities_list:
                    key = (min(c1, c2), max(c1, c2))
                    undirected_flight_set.add(key)
    
    for c1 in cities_list:
        for c2 in cities_list:
            if c1 == c2:
                continue
            key = (min(c1, c2), max(c1, c2))
            flight_exists = key in undirected_flight_set
            s.add(Implies(Or(O[c1] == O[c2] + 1, O[c2] == O[c1] + 1), flight_exists))
            s.add(Implies(O[c1] == O[c2] + 1, A[c1] == D[c2]))
            s.add(Implies(O[c2] == O[c1] + 1, A[c2] == D[c1]))
    
    for city in cities_list:
        s.add(A[city] >= 1)
        s.add(D[city] <= 32)
        s.add(D[city] >= A[city])
    
    if s.check() == sat:
        m = s.model()
        order_vals = []
        for city in cities_list:
            order_val = m.evaluate(O[city])
            a_val = m.evaluate(A[city])
            d_val = m.evaluate(D[city])
            order_vals.append((int(str(order_val)), city, int(str(a_val)), int(str(d_val))))
        
        order_vals.sort(key=lambda x: x[0])
        print("Trip Plan:")
        for order, city, a, d in order_vals:
            print(f"Visit {city} from day {a} to day {d}")
        print("\nTravel itinerary:")
        for i in range(len(order_vals) - 1):
            curr_city = order_vals[i][1]
            next_city = order_vals[i+1][1]
            travel_day = order_vals[i][3]
            print(f"On day {travel_day}, fly from {curr_city} to {next_city}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()