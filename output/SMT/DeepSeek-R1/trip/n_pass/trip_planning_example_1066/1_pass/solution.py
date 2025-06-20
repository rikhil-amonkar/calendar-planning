from z3 import *
import json

def main():
    cities = ["Brussels", "Bucharest", "Stuttgart", "Mykonos", "Helsinki", "Split", "London"]
    days_map = {
        "Brussels": 4,
        "Bucharest": 3,
        "Stuttgart": 4,
        "Mykonos": 2,
        "Helsinki": 5,
        "Split": 3,
        "London": 5
    }
    
    direct_flights = [
        ("Helsinki", "London"),
        ("Split", "Madrid"),
        ("Helsinki", "Madrid"),
        ("London", "Madrid"),
        ("Brussels", "London"),
        ("Bucharest", "London"),
        ("Brussels", "Bucharest"),
        ("Bucharest", "Madrid"),
        ("Split", "Helsinki"),
        ("Mykonos", "Madrid"),
        ("Stuttgart", "London"),
        ("Helsinki", "Brussels"),
        ("Brussels", "Madrid"),
        ("Split", "London"),
        ("Stuttgart", "Split"),
        ("London", "Mykonos")
    ]
    
    pos = [String(f"pos{i}") for i in range(7)]
    s = Solver()
    
    for i in range(7):
        s.add(Or([pos[i] == StringVal(city) for city in cities]))
    s.add(Distinct(pos))
    
    def day(city_expr):
        return If(city_expr == StringVal("Brussels"), 4,
               If(city_expr == StringVal("Bucharest"), 3,
               If(city_expr == StringVal("Stuttgart"), 4,
               If(city_expr == StringVal("Mykonos"), 2,
               If(city_expr == StringVal("Helsinki"), 5,
               If(city_expr == StringVal("Split"), 3,
               If(city_expr == StringVal("London"), 5, 0)))))))
    
    P = [0] * 8
    P[0] = 0
    for i in range(1, 8):
        P[i] = P[i-1] + day(pos[i-1])
    
    for i in range(6):
        c1 = pos[i]
        c2 = pos[i+1]
        valid = False
        for flight in direct_flights:
            a, b = flight
            a_str = StringVal(a)
            b_str = StringVal(b)
            valid = Or(valid, And(c1 == a_str, c2 == b_str), And(c1 == b_str, c2 == a_str))
        s.add(valid)
    
    valid_last = False
    madrid_val = StringVal("Madrid")
    for flight in direct_flights:
        a, b = flight
        a_str = StringVal(a)
        b_str = StringVal(b)
        valid_last = Or(valid_last, And(pos[6] == a_str, madrid_val == b_str), And(pos[6] == b_str, madrid_val == a_str))
    s.add(valid_last)
    
    for i in range(1, 7):
        s.add(Implies(pos[i] == StringVal("Stuttgart"), P[i] - (i-1) <= 4))
    
    if s.check() == sat:
        m = s.model()
        city_seq = []
        for i in range(7):
            city_expr = m.evaluate(pos[i])
            city_name = city_expr.as_string()
            city_name = city_name.strip('"')
            city_seq.append(city_name)
        
        P_actual = [0] * 8
        P_actual[0] = 0
        for i in range(7):
            city = city_seq[i]
            P_actual[i+1] = P_actual[i] + days_map[city]
        
        records = []
        start0 = 1
        end0 = P_actual[1]
        records.append({"day_range": f"Day {start0}-{end0}", "place": city_seq[0]})
        records.append({"day_range": f"Day {end0}", "place": city_seq[0]})
        
        for i in range(1, 7):
            start_i = P_actual[i] - (i-1)
            end_i = P_actual[i+1] - i
            records.append({"day_range": f"Day {start_i}", "place": city_seq[i]})
            records.append({"day_range": f"Day {start_i}-{end_i}", "place": city_seq[i]})
            records.append({"day_range": f"Day {end_i}", "place": city_seq[i]})
        
        records.append({"day_range": "Day 20", "place": "Madrid"})
        records.append({"day_range": "Day 20-21", "place": "Madrid"})
        
        result = {"itinerary": records}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()