from z3 import *
import json

def main():
    City = Datatype('City')
    City.declare('Hamburg')
    City.declare('Munich')
    City.declare('Manchester')
    City.declare('Lyon')
    City.declare('Split')
    City = City.create()
    
    city_map = {
        "Hamburg": City.Hamburg,
        "Munich": City.Munich,
        "Manchester": City.Manchester,
        "Lyon": City.Lyon,
        "Split": City.Split
    }
    
    rev_map = {
        City.Hamburg: "Hamburg",
        City.Munich: "Munich",
        City.Manchester: "Manchester",
        City.Lyon: "Lyon",
        City.Split: "Split"
    }
    
    P = [Const(f'P{i}', City) for i in range(21)]
    
    s = Solver()
    
    directed_flights = set()
    bidirectional_edges = [
        ("Split", "Munich"),
        ("Munich", "Manchester"),
        ("Hamburg", "Manchester"),
        ("Hamburg", "Munich"),
        ("Split", "Lyon"),
        ("Lyon", "Munich"),
        ("Hamburg", "Split")
    ]
    unidirectional_edges = [("Manchester", "Split")]
    
    for u, v in bidirectional_edges:
        u_const = city_map[u]
        v_const = city_map[v]
        directed_flights.add((u_const, v_const))
        directed_flights.add((v_const, u_const))
    
    for u, v in unidirectional_edges:
        u_const = city_map[u]
        v_const = city_map[v]
        directed_flights.add((u_const, v_const))
    
    for i in range(19):
        current = P[i]
        next_city = P[i+1]
        flight_constraint = Or([And(current == u, next_city == v) for u, v in directed_flights])
        s.add(If(current != next_city, flight_constraint, True))
    
    def consecutive_stay(city, days, total_days=20):
        start_indices = range(0, total_days - days + 1)
        constraints = []
        for start in start_indices:
            block = [P[i] == city for i in range(start, start + days)]
            outside = []
            for i in range(total_days):
                if i < start or i >= start + days:
                    outside.append(P[i] != city)
            constraints.append(And(block + outside))
        s.add(Or(constraints))
    
    consecutive_stay(City.Hamburg, 7)
    consecutive_stay(City.Split, 7)
    
    s.add(P[12] == City.Lyon)
    s.add(Sum([If(P[i] == City.Lyon, 1, 0) for i in range(20)]) == 2)
    
    s.add(P[18] == City.Manchester)
    s.add(P[19] == City.Manchester)
    for i in range(18):
        s.add(P[i] != City.Manchester)
    
    s.add(Sum([If(P[i] == City.Munich, 1, 0) for i in range(20)]) == 2)
    
    if s.check() == sat:
        model = s.model()
        current_city = model[P[0]]
        start_day = 1
        itinerary = []
        
        for day in range(1, 21):
            i = day - 1
            if model[P[i]] != current_city:
                end_day = day - 1
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary.append({
                    "day_range": day_range,
                    "place": rev_map[current_city.as_long()]
                })
                start_day = day
                current_city = model[P[i]]
        
        if start_day == 20:
            day_range = "Day 20"
        else:
            day_range = f"Day {start_day}-20"
        itinerary.append({
            "day_range": day_range,
            "place": rev_map[current_city.as_long()]
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()