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
        total = 0
        # Day 1
        total += If(c[0] == city, 1, 0)
        # Days 2 to 19
        for j in range(2, 20):
            # Check if either:
            # 1. Overnight at end of day j is in the city
            # 2. Departure from city on day j (overnight at end of day j-1 was in city and different at end of day j)
            total += If(Or(c[j-1] == city, 
                           And(c[j-2] == city, c[j-1] != city)), 
                        1, 0)
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
            return Or(c[day-1] == city, 
                      And(c[day-2] == city, c[day-1] != city))
    
    s.add(Or(in_city(5, Istanbul), in_city(6, Istanbul), in_city(7, Istanbul), in_city(8, Istanbul)))
    s.add(Or(in_city(8, Oslo), in_city(9, Oslo)))
    
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        current_city = model.evaluate(c[0])
        start_day = 1
        for day in range(1, 19):
            if model.evaluate(c[day]) != current_city:
                end_day = day
                itinerary_list.append({
                    'day_range': f'Day {start_day}-{end_day}' if start_day != end_day else f'Day {start_day}',
                    'place': str(current_city)
                })
                start_day = day + 1
                current_city = model.evaluate(c[day])
        itinerary_list.append({
            'day_range': f'Day {start_day}-19' if start_day != 19 else 'Day 19',
            'place': str(current_city)
        })
        
        result = {
            "itinerary": itinerary_list
        }
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()