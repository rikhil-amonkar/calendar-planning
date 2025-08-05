import z3
import json

def main():
    City = z3.Datatype('City')
    City.declare('Prague')
    City.declare('Stuttgart')
    City.declare('Split')
    City.declare('Krakow')
    City.declare('Florence')
    City = City.create()
    
    flight_set = [
        (City.Stuttgart, City.Split),
        (City.Prague, City.Florence),
        (City.Krakow, City.Stuttgart),
        (City.Krakow, City.Split),
        (City.Split, City.Prague),
        (City.Krakow, City.Prague)
    ]
    
    c = [z3.Const('c%d' % i, City) for i in range(9)]
    
    s = z3.Solver()
    
    for i in range(1, 9):
        c_prev = c[i-1]
        c_curr = c[i]
        conds = []
        for (a, b) in flight_set:
            conds.append(z3.And(c_prev == a, c_curr == b))
            conds.append(z3.And(c_prev == b, c_curr == a))
        flight_ok = z3.Or(conds)
        s.add(z3.If(c_prev == c_curr, True, flight_ok))
    
    cities_list = [City.Prague, City.Stuttgart, City.Split, City.Krakow, City.Florence]
    total_days = {}
    for city in cities_list:
        total = 0
        for i in range(1, 9):
            total += z3.If(z3.Or(c[i-1] == city, c[i] == city), 1, 0)
        total_days[city] = total
    
    s.add(total_days[City.Prague] == 4)
    s.add(total_days[City.Stuttgart] == 2)
    s.add(total_days[City.Split] == 2)
    s.add(total_days[City.Krakow] == 2)
    s.add(total_days[City.Florence] == 2)
    
    s.add(z3.Or(c[1] == City.Stuttgart, c[2] == City.Stuttgart, c[3] == City.Stuttgart))
    s.add(z3.Or(c[2] == City.Split, c[3] == City.Split, c[4] == City.Split))
    
    if s.check() == z3.sat:
        m = s.model()
        itinerary = []
        for day in range(1, 9):
            prev_city = m.evaluate(c[day-1])
            curr_city = m.evaluate(c[day])
            if prev_city.eq(curr_city):
                itinerary.append({
                    'day_range': f'Day {day}-1',
                    'place': str(prev_city)
                })
            else:
                itinerary.append({
                    'day_range': f'Day {day}-1',
                    'place': str(prev_city)
                })
                itinerary.append({
                    'day_range': f'Day {day}-2',
                    'place': str(curr_city)
                })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()