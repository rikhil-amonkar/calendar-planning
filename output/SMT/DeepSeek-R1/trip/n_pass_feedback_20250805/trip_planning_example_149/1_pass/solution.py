import z3
import json

def main():
    cities = ['Istanbul', 'London', 'Santorini']
    city = [z3.Int('city_%d' % i) for i in range(11)]
    s = z3.Solver()
    
    for i in range(11):
        s.add(z3.Or(city[i] == 0, city[i] == 1, city[i] == 2))
    
    for i in range(1, 11):
        s.add(z3.Or(
            city[i-1] == city[i],
            z3.And(city[i-1] == 0, city[i] == 1),
            z3.And(city[i-1] == 1, city[i] == 0),
            z3.And(city[i-1] == 1, city[i] == 2),
            z3.And(city[i-1] == 2, city[i] == 1)
        ))
    
    def count_days(c):
        return z3.Sum([z3.If(z3.Or(city[i-1] == c, city[i] == c), 1, 0) for i in range(1, 11)])
    
    s.add(count_days(0) == 3)  # Istanbul
    s.add(count_days(1) == 3)  # London
    s.add(count_days(2) == 6)  # Santorini
    
    s.add(z3.Or(city[4] == 2, city[5] == 2))  # Day 5
    s.add(z3.Or(city[9] == 2, city[10] == 2)) # Day 10
    
    if s.check() == z3.sat:
        m = s.model()
        city_vals = [m.evaluate(city[i]) for i in range(11)]
        city_vals = [val.as_long() for val in city_vals]
        
        itinerary_list = []
        for day in range(1, 11):
            if day == 5 or day == 10:
                itinerary_list.append("Santorini")
            else:
                c_index = city_vals[day]
                itinerary_list.append(cities[c_index])
        
        itinerary_output = [{"day": day, "city": city_name} for day, city_name in enumerate(itinerary_list, start=1)]
        result = {"itinerary": itinerary_output}
        print(json.dumps(result))
    else:
        print('"unsat"')

if __name__ == '__main__':
    main()