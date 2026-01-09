import json
from constraint import Problem

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ['Seville', 'Paris', 'Krakow']
    required_days = {
        'Seville': 6,
        'Paris': 2,
        'Krakow': 5
    }
    
    # Total days
    total_days = 11
    
    # Direct flight connections
    connections = {
        'Krakow': ['Paris'],
        'Paris': ['Krakow', 'Seville'],
        'Seville': ['Paris']
    }
    
    # Variables: order of cities to visit (3 slots for 3 cities)
    # Each variable represents which city we're in during that segment
    problem.addVariable("city1", cities)
    problem.addVariable("city2", cities)
    problem.addVariable("city3", cities)
    
    # Variables: duration in each city segment (in days)
    problem.addVariable("days1", range(1, total_days - 1))
    problem.addVariable("days2", range(1, total_days - 1))
    problem.addVariable("days3", range(1, total_days - 1))
    
    # Constraint 1: All three cities must be visited
    def all_cities_visited(c1, c2, c3):
        return len(set([c1, c2, c3])) == 3
    
    problem.addConstraint(all_cities_visited, ["city1", "city2", "city3"])
    
    # Constraint 2: Total days must equal 11
    def total_days_constraint(d1, d2, d3):
        return d1 + d2 + d3 == total_days
    
    problem.addConstraint(total_days_constraint, ["days1", "days2", "days3"])
    
    # Constraint 3: Required days for each city must be met
    def required_days_constraint(c1, c2, c3, d1, d2, d3):
        city_days = {}
        for city, days in [(c1, d1), (c2, d2), (c3, d3)]:
            city_days[city] = city_days.get(city, 0) + days
        
        for city, required in required_days.items():
            if city_days.get(city, 0) != required:
                return False
        return True
    
    problem.addConstraint(required_days_constraint, 
                         ["city1", "city2", "city3", "days1", "days2", "days3"])
    
    # Constraint 4: Direct flights between consecutive cities
    def flight_connection(c1, c2, c3):
        # Check if city1 to city2 has direct flight
        if c1 != c2 and c2 not in connections.get(c1, []):
            return False
        # Check if city2 to city3 has direct flight  
        if c2 != c3 and c3 not in connections.get(c2, []):
            return False
        return True
    
    problem.addConstraint(flight_connection, ["city1", "city2", "city3"])
    
    # Constraint 5: Krakow workshop constraint (Krakow must be visited between day 1-5)
    def krakow_workshop(c1, c2, c3, d1, d2, d3):
        # Find when Krakow is visited
        segments = [(c1, d1), (c2, d2), (c3, d3)]
        
        current_day = 1
        for city, duration in segments:
            if city == 'Krakow':
                # Check if Krakow visit ends by day 5 at the latest
                if current_day + duration - 1 <= 5:
                    return True
            current_day += duration
        
        return False
    
    problem.addConstraint(krakow_workshop, 
                         ["city1", "city2", "city3", "days1", "days2", "days3"])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        result = {"error": "No valid itinerary found"}
        print(json.dumps(result))
        return
    
    # Use the first valid solution
    sol = solutions[0]
    
    # Build itinerary
    itinerary = []
    current_day = 1
    
    segments = [
        (sol['city1'], sol['days1']),
        (sol['city2'], sol['days2']), 
        (sol['city3'], sol['days3'])
    ]
    
    for city, duration in segments:
        end_day = current_day + duration - 1
        if duration == 1:
            day_range = f"Day {current_day}"
        else:
            day_range = f"Day {current_day}-{end_day}"
        
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
        
        current_day = end_day + 1
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()