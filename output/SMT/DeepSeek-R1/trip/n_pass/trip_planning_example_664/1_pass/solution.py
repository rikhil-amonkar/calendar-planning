from z3 import *

def main():
    s = Solver()

    cities = ['Bucharest', 'Munich', 'Seville', 'Milan', 'Stockholm', 'Tallinn']
    start = {city: Int(f'start_{city}') for city in cities}
    end = {city: Int(f'end_{city}') for city in cities}

    durations = {
        'Bucharest': 4,
        'Munich': 5,
        'Seville': 5,
        'Milan': 2,
        'Stockholm': 5,
        'Tallinn': 2
    }

    for city in cities:
        s.add(end[city] - start[city] + 1 == durations[city])

    s.add(start['Bucharest'] >= 1, end['Bucharest'] <= 4)
    s.add(start['Munich'] >= 4, end['Munich'] <= 8)
    s.add(start['Seville'] >= 8, end['Seville'] <= 12)

    flight_connections = [
        ('Bucharest', 'Munich'),
        ('Munich', 'Seville'),
        ('Seville', 'Milan'),
        ('Milan', 'Stockholm'),
        ('Stockholm', 'Tallinn')
    ]

    s.add(start['Bucharest'] == 1)
    s.add(start['Munich'] == end['Bucharest'])
    s.add(start['Seville'] == end['Munich'])
    s.add(start['Milan'] == end['Seville'])
    s.add(start['Stockholm'] == end['Milan'])
    s.add(start['Tallinn'] == end['Stockholm'])
    s.add(end['Tallinn'] == 18)

    if s.check() == sat:
        model = s.model()
        start_vals = {city: model.eval(start[city]).as_long() for city in cities}
        end_vals = {city: model.eval(end[city]).as_long() for city in cities}

        itinerary = []
        for i, city in enumerate(cities):
            if i > 0:
                prev_city = cities[i-1]
                flight_day = end_vals[prev_city]
                itinerary.append({"day_range": f"Day {flight_day}", "place": prev_city})
                itinerary.append({"day_range": f"Day {flight_day}", "place": city})
            itinerary.append({"day_range": f"Day {start_vals[city]}-{end_vals[city]}", "place": city})
        itinerary.append({"day_range": f"Day {end_vals['Tallinn']}", "place": "Tallinn"})

        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()