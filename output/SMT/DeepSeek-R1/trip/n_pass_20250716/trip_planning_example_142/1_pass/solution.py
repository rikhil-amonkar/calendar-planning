from z3 import *
import json

def main():
    # Create solver
    s = Solver()
    
    # Days and cities
    days = list(range(1, 8))  # Day 1 to 7
    cities = ['Madrid', 'Dublin', 'Tallinn']
    
    # Create a dictionary for presence variables: present[(day, city)] = Bool
    present = {}
    for day in days:
        for city in cities:
            present[(day, city)] = Bool(f"present_{day}_{city}")
    
    # Constraint 1: For each day, at least one city and at most two cities.
    for day in days:
        bools = [present[(day, city)] for city in cities]
        s.add(Or(bools))  # At least one city
        s.add(Not(And(bools[0], bools[1], bools[2])))  # At most two cities
    
    # Constraint 2: Adjacent cities for flight days.
    # Forbid Madrid and Tallinn together on any day (no direct flight)
    for day in days:
        s.add(Not(And(present[(day, 'Madrid')], present[(day, 'Tallinn')])))
    
    # Constraint 3: Consecutive days must share at least one city.
    for day in range(1, 7):
        common = Or(
            And(present[(day, 'Madrid')], present[(day+1, 'Madrid')]),
            And(present[(day, 'Dublin')], present[(day+1, 'Dublin')]),
            And(present[(day, 'Tallinn')], present[(day+1, 'Tallinn')])
        )
        s.add(common)
    
    # Constraint 4: Total days per city.
    s.add(Sum([If(present[(d, 'Madrid')], 1, 0) for d in days]) == 4)
    s.add(Sum([If(present[(d, 'Dublin')], 1, 0) for d in days]) == 3)
    s.add(Sum([If(present[(d, 'Tallinn')], 1, 0) for d in days]) == 2)
    
    # Constraint 5: Workshop in Tallinn on days 6 and 7.
    s.add(present[(6, 'Tallinn')])
    s.add(present[(7, 'Tallinn')])
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        
        # Extract the presence values
        itinerary_list = []
        
        # Step 1: Collect contiguous intervals for each city
        intervals_by_city = {city: [] for city in cities}
        for city in cities:
            days_list = []
            for day in days:
                if model.evaluate(present[(day, city)]):
                    days_list.append(day)
            if not days_list:
                continue
            days_list.sort()
            start = days_list[0]
            end = days_list[0]
            for i in range(1, len(days_list)):
                if days_list[i] == end + 1:
                    end = days_list[i]
                else:
                    intervals_by_city[city].append((start, end))
                    start = days_list[i]
                    end = days_list[i]
            intervals_by_city[city].append((start, end))
        
        # Step 2: Identify flight days (days with two cities)
        flight_days = []
        for day in days:
            count = 0
            for city in cities:
                if model.evaluate(present[(day, city)]):
                    count += 1
            if count == 2:
                flight_days.append(day)
        
        # Step 3: For each flight day, determine departure and arrival cities
        flight_day_records = {}
        for d in flight_days:
            cities_d = [city for city in cities if model.evaluate(present[(d, city)])]
            if d < 7:
                next_cities = [city for city in cities if model.evaluate(present[(d+1, city)])]
                common = set(cities_d) & set(next_cities)
                if len(common) == 1:
                    arrival_city = common.pop()
                    departure_city = [c for c in cities_d if c != arrival_city][0]
                else:
                    departure_city = cities_d[0]
                    arrival_city = cities_d[1]
            else:
                departure_city = cities_d[0]
                arrival_city = cities_d[1]
            flight_day_records[d] = [
                {"day_range": f"Day {d}", "place": departure_city},
                {"day_range": f"Day {d}", "place": arrival_city}
            ]
        
        # Step 4: Build the itinerary list in chronological order
        events = []
        for d in days:
            if d in flight_day_records:
                events.extend(flight_day_records[d])
            for city in cities:
                for (start, end) in intervals_by_city[city]:
                    if start == d:
                        if start == end:
                            day_range_str = f"Day {start}"
                        else:
                            day_range_str = f"Day {start}-{end}"
                        events.append({"day_range": day_range_str, "place": city})
        
        result = {"itinerary": events}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()