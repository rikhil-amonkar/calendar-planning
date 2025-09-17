from z3 import *
import json

def main():
    cities = ["Paris", "Warsaw", "Krakow", "Tallinn", "Riga", "Copenhagen", "Helsinki", "Oslo", "Santorini", "Lyon"]
    req_days = [5, 2, 2, 2, 2, 5, 5, 5, 2, 4]
    
    flight_str = """Warsaw and Riga, Warsaw and Tallinn, Copenhagen and Helsinki, Lyon and Paris, Copenhagen and Warsaw, Lyon and Oslo, Paris and Oslo, Paris and Riga, Krakow and Helsinki, Paris and Tallinn, Oslo and Riga, Krakow and Warsaw, Paris and Helsinki, Copenhagen and Santorini, Helsinki and Warsaw, Helsinki and Riga, Copenhagen and Krakow, Copenhagen and Riga, Paris and Krakow, Copenhagen and Oslo, Oslo and Tallinn, Oslo and Helsinki, Copenhagen and Tallinn, Oslo and Krakow, from Riga to Tallinn, Helsinki and Tallinn, Paris and Copenhagen, Paris and Warsaw, from Santorini to Oslo, Oslo and Warsaw"""
    
    allowed_flights = set()
    tokens = flight_str.split(',')
    for token in tokens:
        token = token.strip()
        if token.startswith('from'):
            parts = token.split()
            from_city = parts[1]
            to_city = parts[3]
            allowed_flights.add((from_city, to_city))
        else:
            parts = token.split(' and ')
            city1 = parts[0].strip()
            city2 = parts[1].strip()
            allowed_flights.add((city1, city2))
            allowed_flights.add((city2, city1))
    
    allowed_tuples = []
    for (from_city, to_city) in allowed_flights:
        from_index = cities.index(from_city)
        to_index = cities.index(to_city)
        allowed_tuples.append((from_index, to_index))
    
    morning = [Int('morning_%d' % i) for i in range(1,26)]
    evening = [Int('evening_%d' % i) for i in range(1,26)]
    
    s = Solver()
    
    for i in range(25):
        s.add(And(morning[i] >= 0, morning[i] < 10))
        s.add(And(evening[i] >= 0, evening[i] < 10))
    
    s.add(morning[0] == evening[0])
    
    for i in range(1,25):
        s.add(morning[i] == evening[i-1])
    
    for i in range(25):
        condition = Or([And(morning[i] == fr, evening[i] == to) for (fr, to) in allowed_tuples])
        s.add(If(morning[i] != evening[i], condition, True))
    
    for c in range(10):
        total = 0
        for i in range(25):
            total += If(Or(morning[i] == c, evening[i] == c), 1, 0)
        s.add(total == req_days[c])
    
    paris_index = cities.index("Paris")
    for d in [3,4,5,6,7]:
        s.add(Or(morning[d] == paris_index, evening[d] == paris_index))
    
    krakow_index = cities.index("Krakow")
    for d in [16,17]:
        s.add(Or(morning[d] == krakow_index, evening[d] == krakow_index))
    
    riga_index = cities.index("Riga")
    for d in [22,23]:
        s.add(Or(morning[d] == riga_index, evening[d] == riga_index))
    
    helsinki_index = cities.index("Helsinki")
    s.add(Or([Or(morning[d] == helsinki_index, evening[d] == helsinki_index) for d in range(17,22)]))
    
    santorini_index = cities.index("Santorini")
    s.add(Or(Or(morning[11] == santorini_index, evening[11] == santorini_index),
             Or(morning[12] == santorini_index, evening[12] == santorini_index)))
    
    if s.check() == sat:
        m = s.model()
        morning_val = [m.evaluate(morning[i]) for i in range(25)]
        evening_val = [m.evaluate(evening[i]) for i in range(25)]
        morning_int = [int(morning_val[i].as_string()) for i in range(25)]
        evening_int = [int(evening_val[i].as_string()) for i in range(25)]
        
        segments = []
        current_city = evening_int[0]
        start = 1
        for day in range(1,25):
            if evening_int[day] != current_city:
                segments.append({"day_range": f"Day {start}-{day}", "place": cities[current_city]})
                start = day + 1
                current_city = evening_int[day]
        segments.append({"day_range": f"Day {start}-25", "place": cities[current_city]})
        
        print(json.dumps({"itinerary": segments}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()