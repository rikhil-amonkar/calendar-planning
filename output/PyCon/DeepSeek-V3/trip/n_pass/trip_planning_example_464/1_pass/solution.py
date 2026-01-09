import json
from constraint import Problem

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ["Krakow", "Frankfurt", "Oslo", "Dubrovnik", "Naples"]
    required_days = {
        "Krakow": 5,
        "Frankfurt": 4, 
        "Oslo": 3,
        "Dubrovnik": 5,
        "Naples": 5
    }
    
    # Direct flight connections
    connections = {
        "Dubrovnik": ["Oslo", "Frankfurt", "Naples"],
        "Frankfurt": ["Krakow", "Oslo", "Dubrovnik", "Naples"],
        "Krakow": ["Frankfurt", "Oslo"],
        "Oslo": ["Dubrovnik", "Frankfurt", "Krakow", "Naples"],
        "Naples": ["Oslo", "Dubrovnik", "Frankfurt"]
    }
    
    # Total days
    total_days = 18
    
    # Special constraints
    # Oslo must be between day 16-18 (inclusive)
    # Dubrovnik must have some days between day 5-9 (inclusive)
    
    # We'll model this as finding the order of cities and their durations
    # Since we have 5 cities and 4 transitions, we need to find:
    # - The order of cities (5 positions)
    # - The number of days in each city (must sum to 18)
    
    # Add variables for city order
    for i in range(5):
        problem.addVariable(f'city_{i}', cities)
    
    # Add variables for days in each city position
    for i in range(5):
        problem.addVariable(f'days_{i}', range(1, total_days - 3))  # At least 1 day per city
    
    # All cities must be visited exactly once
    problem.addConstraint(lambda c0, c1, c2, c3, c4: 
                         len(set([c0, c1, c2, c3, c4])) == 5, 
                         ['city_0', 'city_1', 'city_2', 'city_3', 'city_4'])
    
    # Total days must sum to 18
    problem.addConstraint(lambda d0, d1, d2, d3, d4: d0 + d1 + d2 + d3 + d4 == total_days,
                         ['days_0', 'days_1', 'days_2', 'days_3', 'days_4'])
    
    # Each city must get the required number of days
    def days_constraint(c0, c1, c2, c3, c4, d0, d1, d2, d3, d4):
        city_days = {}
        for city, days in zip([c0, c1, c2, c3, c4], [d0, d1, d2, d3, d4]):
            city_days[city] = city_days.get(city, 0) + days
        
        for city, req_days in required_days.items():
            if city_days.get(city, 0) != req_days:
                return False
        return True
    
    problem.addConstraint(days_constraint, 
                         ['city_0', 'city_1', 'city_2', 'city_3', 'city_4',
                          'days_0', 'days_1', 'days_2', 'days_3', 'days_4'])
    
    # Flight connections constraint - consecutive cities must be connected
    def connection_constraint(c1, c2):
        return c2 in connections[c1]
    
    for i in range(4):
        problem.addConstraint(connection_constraint, [f'city_{i}', f'city_{i+1}'])
    
    # Special time window constraints
    def time_constraint(c0, c1, c2, c3, c4, d0, d1, d2, d3, d4):
        # Calculate cumulative days to determine when we're in each city
        cumulative = [d0, d0 + d1, d0 + d1 + d2, d0 + d1 + d2 + d3, d0 + d1 + d2 + d3 + d4]
        
        # Find which position contains Oslo and Dubrovnik
        city_order = [c0, c1, c2, c3, c4]
        
        # Check Oslo constraint (days 16-18)
        oslo_positions = [i for i, city in enumerate(city_order) if city == "Oslo"]
        if not oslo_positions:
            return False
            
        oslo_idx = oslo_positions[0]
        if oslo_idx == 0:
            oslo_start = 1
            oslo_end = d0
        else:
            oslo_start = cumulative[oslo_idx - 1] + 1
            oslo_end = cumulative[oslo_idx]
        
        # Oslo must include days 16, 17, 18
        if not (oslo_start <= 16 and oslo_end >= 18):
            return False
        
        # Check Dubrovnik constraint (some days between 5-9)
        dubrovnik_positions = [i for i, city in enumerate(city_order) if city == "Dubrovnik"]
        if not dubrovnik_positions:
            return False
            
        dubrovnik_idx = dubrovnik_positions[0]
        if dubrovnik_idx == 0:
            dubrovnik_start = 1
            dubrovnik_end = d0
        else:
            dubrovnik_start = cumulative[dubrovnik_idx - 1] + 1
            dubrovnik_end = cumulative[dubrovnik_idx]
        
        # Dubrovnik must have some overlap with days 5-9
        if not (dubrovnik_start <= 9 and dubrovnik_end >= 5):
            return False
            
        return True
    
    problem.addConstraint(time_constraint, 
                         ['city_0', 'city_1', 'city_2', 'city_3', 'city_4',
                          'days_0', 'days_1', 'days_2', 'days_3', 'days_4'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first valid solution
    sol = solutions[0]
    
    # Build itinerary
    itinerary = []
    current_day = 1
    
    for i in range(5):
        city = sol[f'city_{i}']
        days = sol[f'days_{i}']
        end_day = current_day + days - 1
        
        if days == 1:
            day_range = f"Day {current_day}"
        else:
            day_range = f"Day {current_day}-{end_day}"
            
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
        
        current_day = end_day + 1
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()