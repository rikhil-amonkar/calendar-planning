from z3 import *

def main():
    City, (Reykjavik, Istanbul, Edinburgh, Oslo, Stuttgart, Bucharest) = EnumSort('City', [
        'Reykjavik',
        'Istanbul',
        'Edinburgh',
        'Oslo',
        'Stuttgart',
        'Bucharest'
    ])
    
    c = [Const('c_%d' % i, City) for i in range(19)]
    
    s = Solver()
    
    allowed_flights = [
        (Bucharest, Oslo), (Oslo, Bucharest),
        (Istanbul, Oslo), (Oslo, Istanbul),
        (Reykjavik, Stuttgart),
        (Bucharest, Istanbul), (Istanbul, Bucharest),
        (Stuttgart, Edinburgh), (Edinburgh, Stuttgart),
        (Istanbul, Edinburgh), (Edinburgh, Istanbul),
        (Oslo, Reykjavik), (Reykjavik, Oslo),
        (Istanbul, Stuttgart), (Stuttgart, Istanbul),
        (Oslo, Edinburgh), (Edinburgh, Oslo)
    ]
    
    for i in range(18):
        s.add(Or(
            c[i] == c[i+1],
            Or([And(c[i] == a, c[i+1] == b) for (a, b) in allowed_flights])
        ))
    
    def total_days(city):
        total = If(c[0] == city, 1, 0)
        for i in range(1, 19):
            total += If(Or(c[i-1] == city, c[i] == city), 1, 0)
        return total
    
    s.add(total_days(Reykjavik) == 5)
    s.add(total_days(Istanbul) == 4)
    s.add(total_days(Edinburgh) == 5)
    s.add(total_days(Oslo) == 2)
    s.add(total_days(Stuttgart) == 3)
    s.add(total_days(Bucharest) == 5)
    
    def in_city(day, city):
        if day == 1:
            return c[0] == city
        else:
            return Or(c[day-2] == city, c[day-1] == city)
    
    s.add(Or(in_city(5, Istanbul), in_city(6, Istanbul), in_city(7, Istanbul), in_city(8, Istanbul)))
    s.add(Or(in_city(8, Oslo), in_city(9, Oslo)))
    
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        for day in range(1, 20):
            city_val = model.evaluate(c[day-1])
            city_name = str(city_val)
            itinerary_list.append({"day": day, "place": city_name})
        
        result = {
            "itinerary": itinerary_list
        }
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()