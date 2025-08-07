from z3 import *
import json

def main():
    # Define the cities and their enum sort
    CitySort, cities_const = EnumSort('City', ['Paris', 'Madrid', 'Bucharest', 'Seville'])
    paris, madrid, bucharest, seville = cities_const
    cities_names = ['Paris', 'Madrid', 'Bucharest', 'Seville']
    
    # Create variables d0 to d15
    d = [Const('d_%d' % i, CitySort) for i in range(0, 16)]
    
    s = Solver()
    
    # Define direct flight connections (undirected)
    flights = [
        (paris, bucharest),
        (seville, paris),
        (madrid, bucharest),
        (madrid, paris),
        (madrid, seville)
    ]
    
    # Helper function to check flight connection
    def is_connected(c1, c2):
        options = []
        for (city1, city2) in flights:
            options.append(And(c1 == city1, c2 == city2))
            options.append(And(c1 == city2, c2 == city1))
        return Or(options)
    
    # Flight constraints for days 1 to 15
    for i in range(1, 16):
        s.add(If(d[i-1] != d[i], is_connected(d[i-1], d[i]), True))
    
    # Madrid must be present on days 1 to 7 and absent on days 8 to 15
    for i in range(1, 8):  # days 1 to 7
        s.add(Or(d[i-1] == madrid, d[i] == madrid))
    for i in range(8, 16):  # days 8 to 15
        s.add(Not(Or(d[i-1] == madrid, d[i] == madrid)))
    
    # Bucharest must not be present on days 1 to 13 and must be present on days 14 to 15
    for i in range(1, 14):  # days 1 to 13
        s.add(Not(Or(d[i-1] == bucharest, d[i] == bucharest)))
    for i in range(14, 16):  # days 14 to 15
        s.add(Or(d[i-1] == bucharest, d[i] == bucharest))
    
    # Define total days function for a city
    def total_days(city):
        return Sum([If(Or(d[i-1] == city, d[i] == city), 1, 0) for i in range(1, 16)])
    
    # Add constraints for total days in Paris and Seville
    s.add(total_days(paris) == 6)
    s.add(total_days(seville) == 3)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        
        # Helper function to map Z3 constant to city name
        def get_city_name(c):
            for idx, const in enumerate(cities_const):
                if m.eval(const).eq(m.eval(c)):
                    return cities_names[idx]
            return "Unknown"
        
        itinerary = []
        for day in range(1, 16):
            city_prev = d[day-1]
            city_curr = d[day]
            name_prev = get_city_name(city_prev)
            name_curr = get_city_name(city_curr)
            if name_prev == name_curr:
                cities_list = [name_prev]
            else:
                cities_list = [name_prev, name_curr]
                cities_list.sort()
            itinerary.append({"day": day, "cities": cities_list})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()