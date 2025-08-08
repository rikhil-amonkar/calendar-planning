from z3 import *
import json

def main():
    cities = ["Seville", "Vilnius", "Santorini", "London", "Stuttgart", "Dublin", "Frankfurt"]
    city_ids = {city: idx for idx, city in enumerate(cities)}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    days_req = {
        "Seville": 5,
        "Vilnius": 3,
        "Santorini": 2,
        "London": 2,
        "Stuttgart": 3,
        "Dublin": 3,
        "Frankfurt": 5
    }
    
    flight_list = [
        ("Frankfurt", "Dublin"),
        ("Frankfurt", "London"),
        ("London", "Dublin"),
        ("Vilnius", "Frankfurt"),
        ("Frankfurt", "Stuttgart"),
        ("Dublin", "Seville"),
        ("London", "Santorini"),
        ("Stuttgart", "London"),
        ("Santorini", "Dublin")
    ]
    
    directed_flights = []
    for a, b in flight_list:
        id_a = city_ids[a]
        id_b = city_ids[b]
        directed_flights.append((id_a, id_b))
        directed_flights.append((id_b, id_a))
    
    s = Solver()
    
    city_id = [Int(f'city_id_{i}') for i in range(7)]
    for i in range(7):
        s.add(city_id[i] >= 0, city_id[i] <= 6)
    s.add(Distinct(city_id))
    
    duration = [Int(f'duration_{i}') for i in range(7)]
    for i in range(7):
        s.add(duration[i] == 
              If(city_id[i] == city_ids["Seville"], days_req["Seville"],
              If(city_id[i] == city_ids["Vilnius"], days_req["Vilnius"],
              If(city_id[i] == city_ids["Santorini"], days_req["Santorini"],
              If(city_id[i] == city_ids["London"], days_req["London"],
              If(city_id[i] == city_ids["Stuttgart"], days_req["Stuttgart"],
              If(city_id[i] == city_ids["Dublin"], days_req["Dublin"],
                 days_req["Frankfurt"]))))))
    
    cumulative = [Int(f'cumulative_{i}') for i in range(7)]
    s.add(cumulative[0] == 0)
    for i in range(1, 7):
        s.add(cumulative[i] == cumulative[i-1] + (duration[i-1] - 1))
    
    start_day = [Int(f'start_day_{i}') for i in range(7)]
    for i in range(7):
        s.add(start_day[i] == 1 + cumulative[i])
    
    end_day = [Int(f'end_day_{i}') for i in range(7)]
    for i in range(7):
        s.add(end_day[i] == start_day[i] + duration[i] - 1)
    
    s.add(end_day[6] == 17)
    
    for i in range(6):
        constraints = []
        for a, b in directed_flights:
            constraints.append(And(city_id[i] == a, city_id[i+1] == b))
        s.add(Or(constraints))
    
    london_id = city_ids["London"]
    stuttgart_id = city_ids["Stuttgart"]
    
    london_constraints = []
    for i in range(7):
        london_constraints.append(And(city_id[i] == london_id, start_day[i] <= 10, end_day[i] >= 9))
    s.add(Or(london_constraints))
    
    stuttgart_constraints = []
    for i in range(7):
        stuttgart_constraints.append(And(city_id[i] == stuttgart_id, start_day[i] <= 9, end_day[i] >= 7))
    s.add(Or(stuttgart_constraints))
    
    if s.check() == sat:
        m = s.model()
        segments = []
        for i in range(7):
            cid_val = m.evaluate(city_id[i]).as_long()
            city_name = id_to_city[cid_val]
            start_val = m.evaluate(start_day[i]).as_long()
            end_val = m.evaluate(end_day[i]).as_long()
            segments.append((city_name, start_val, end_val))
        
        itinerary = []
        for day in range(1, 18):
            for city, start, end in segments:
                if start <= day <= end:
                    itinerary.append({"day": day, "city": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()