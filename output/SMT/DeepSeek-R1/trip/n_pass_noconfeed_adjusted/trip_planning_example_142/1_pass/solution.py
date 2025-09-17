from z3 import *
import json

def main():
    s = Solver()
    
    cities = ['Madrid', 'Dublin', 'Tallinn']
    Madrid, Dublin, Tallinn = 0, 1, 2
    
    morning = [Int('morning_%d' % i) for i in range(1, 8)]
    evening = [Int('evening_%d' % i) for i in range(1, 8)]
    
    for i in range(7):
        s.add(And(morning[i] >= 0, morning[i] <= 2))
        s.add(And(evening[i] >= 0, evening[i] <= 2))
    
    for i in range(6):
        s.add(evening[i] == morning[i+1])
    
    for i in range(7):
        cond = (morning[i] != evening[i])
        s.add(Implies(cond, 
                      Or(And(morning[i] == Madrid, evening[i] == Dublin),
                         And(morning[i] == Dublin, evening[i] == Madrid),
                         And(morning[i] == Dublin, evening[i] == Tallinn),
                         And(morning[i] == Tallinn, evening[i] == Dublin))))
    
    madrid_days = []
    dublin_days = []
    tallinn_days = []
    for i in range(7):
        madrid_days.append(Or(morning[i] == Madrid, evening[i] == Madrid))
        dublin_days.append(Or(morning[i] == Dublin, evening[i] == Dublin))
        tallinn_days.append(Or(morning[i] == Tallinn, evening[i] == Tallinn))
    
    s.add(Sum([If(b, 1, 0) for b in madrid_days]) == 4)
    s.add(Sum([If(b, 1, 0) for b in dublin_days]) == 3)
    s.add(Sum([If(b, 1, 0) for b in tallinn_days]) == 2)
    
    s.add(tallinn_days[5])
    s.add(tallinn_days[6])
    
    if s.check() == sat:
        m = s.model()
        morning_vals = [m.evaluate(morning[i]).as_long() for i in range(7)]
        evening_vals = [m.evaluate(evening[i]).as_long() for i in range(7)]
        
        city_days = {0: set(), 1: set(), 2: set()}
        for day_index in range(7):
            day_num = day_index + 1
            city_days[morning_vals[day_index]].add(day_num)
            city_days[evening_vals[day_index]].add(day_num)
        
        segments = []
        for city_code, days in city_days.items():
            if days:
                min_day = min(days)
                max_day = max(days)
                segments.append((min_day, max_day, cities[city_code]))
        
        segments.sort(key=lambda x: x[0])
        itinerary_list = [{"day_range": f"Day {start}-{end}", "place": city} for start, end, city in segments]
        
        print(json.dumps({"itinerary": itinerary_list}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()