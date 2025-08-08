from z3 import *
import json

def main():
    # Cities mapping: 0=Mykonos, 1=Budapest, 2=Hamburg
    cities = [0, 1, 2]
    city_names = {0: 'Mykonos', 1: 'Budapest', 2: 'Hamburg'}
    
    # Create Z3 variables for start_city for each day (days 1 to 9)
    start_city = [Int('start_city_%d' % d) for d in range(9)]  # 0-indexed: days 0 to 8 represent days 1 to 9
    
    s = Solver()
    
    # Each day's start city must be one of the three cities
    for i in range(9):
        s.add(Or(start_city[i] == 0, start_city[i] == 1, start_city[i] == 2))
    
    # Flight constraints: if moving between consecutive days, ensure a direct flight exists
    for i in range(8):  # from day i to day i+1 (0-indexed: 0 to 7)
        s.add(
            If(
                start_city[i] != start_city[i+1],
                Or(
                    And(start_city[i] == 0, start_city[i+1] == 1),
                    And(start_city[i] == 1, start_city[i+1] == 0),
                    And(start_city[i] == 1, start_city[i+1] == 2),
                    And(start_city[i] == 2, start_city[i+1] == 1)
                ),
                True  # if staying, no constraint
            )
        )
    
    # Define a helper function to check presence in Mykonos on a given day
    def in_mykonos(day_index):
        if day_index < 8:  # not the last day
            return Or(
                start_city[day_index] == 0,
                And(start_city[day_index] != start_city[day_index+1], start_city[day_index+1] == 0)
            )
        else:  # last day
            return start_city[day_index] == 0
    
    # Constraints for conference days: day4 (index 3) and day9 (index 8) must be in Mykonos
    s.add(in_mykonos(3))  # day4
    s.add(in_mykonos(8))  # day9
    
    # Define a helper function to count days in a city
    def in_city(day_index, city):
        if day_index < 8:
            return Or(
                start_city[day_index] == city,
                And(start_city[day_index] != start_city[day_index+1], start_city[day_index+1] == city)
            )
        else:
            return start_city[day_index] == city
    
    # Total days in each city
    total_mykonos = Sum([If(in_city(i, 0), 1, 0) for i in range(9)])
    total_budapest = Sum([If(in_city(i, 1), 1, 0) for i in range(9)])
    total_hamburg = Sum([If(in_city(i, 2), 1, 0) for i in range(9)])
    
    s.add(total_mykonos == 6)
    s.add(total_budapest == 3)
    s.add(total_hamburg == 2)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        start_vals = [m.evaluate(start_city[i]).as_long() for i in range(9)]
        
        itinerary_list = []
        for j in range(9):  # j from 0 to 8 (days 1 to 9)
            day = j + 1
            if j < 8 and start_vals[j] != start_vals[j+1]:
                cities_on_day = [start_vals[j], start_vals[j+1]]
            else:
                cities_on_day = [start_vals[j]]
            city_names_list = [city_names[c] for c in cities_on_day]
            sorted_cities = sorted(city_names_list)  # Sort alphabetically
            itinerary_list.append({"day": day, "place": sorted_cities})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()