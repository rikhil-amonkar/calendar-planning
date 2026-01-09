import json
from constraint import Problem

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ['Split', 'Vilnius', 'Santorini', 'Madrid']
    required_days = {
        'Split': 5,
        'Vilnius': 4,
        'Santorini': 2,
        'Madrid': 6
    }
    
    # Direct flight connections
    connections = {
        'Vilnius': ['Split'],
        'Split': ['Vilnius', 'Madrid'],
        'Madrid': ['Split', 'Santorini'],
        'Santorini': ['Madrid']
    }
    
    # Total days
    total_days = 14
    
    # Conference constraint: Must be in Santorini on days 13 and 14
    conference_days = [13, 14]
    
    # We need to model the itinerary as a sequence of city stays
    # Each stay is a tuple (city, start_day, end_day)
    # We'll use a constraint satisfaction approach
    
    # Variables: order of cities visited
    # Since we have 4 cities, we need to find the visiting order
    problem.addVariable("visit_order", [('Split', 'Vilnius', 'Madrid', 'Santorini'),
                                      ('Split', 'Madrid', 'Vilnius', 'Santorini'),
                                      ('Vilnius', 'Split', 'Madrid', 'Santorini'),
                                      ('Madrid', 'Split', 'Vilnius', 'Santorini'),
                                      ('Madrid', 'Santorini', 'Split', 'Vilnius')])
    
    # Helper function to check if two cities are connected
    def are_connected(city1, city2):
        return city2 in connections.get(city1, [])
    
    # Constraint: consecutive cities in the order must be connected by direct flights
    def flight_connection_constraint(order):
        for i in range(len(order) - 1):
            if not are_connected(order[i], order[i+1]):
                return False
        return True
    
    problem.addConstraint(flight_connection_constraint, ["visit_order"])
    
    # Function to calculate day ranges for a given order
    def calculate_itinerary(order):
        current_day = 1
        itinerary = []
        
        for i, city in enumerate(order):
            days_needed = required_days[city]
            
            # Special handling for Santorini due to conference
            if city == 'Santorini':
                # Santorini must include days 13-14
                if current_day <= 13 and current_day + days_needed - 1 >= 14:
                    # Current placement works for conference
                    pass
                else:
                    # Need to adjust Santorini to include conference days
                    if i == len(order) - 1:
                        # Last city, place at the end
                        start_day = 14 - days_needed + 1
                        end_day = 14
                    else:
                        # Not last city, need to find placement that works
                        # For simplicity, we'll try to place it to include days 13-14
                        start_day = 13
                        end_day = 14
                        days_needed = 2  # Conference requirement takes precedence
                    
                    itinerary.append({
                        'day_range': f"Day {start_day}-{end_day}",
                        'place': city
                    })
                    current_day = end_day + 1
                    continue
            
            end_day = current_day + days_needed - 1
            
            # Adjust if we exceed total days
            if end_day > total_days:
                end_day = total_days
                days_needed = end_day - current_day + 1
            
            itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            
            current_day = end_day + 1
            
            # Stop if we've used all days
            if current_day > total_days:
                break
        
        return itinerary
    
    # Constraint: itinerary must satisfy all requirements
    def valid_itinerary_constraint(order):
        itinerary = calculate_itinerary(order)
        
        # Check if we used all required days for each city
        city_days = {}
        for stay in itinerary:
            city = stay['place']
            day_range = stay['day_range']
            start, end = map(int, day_range.replace('Day ', '').split('-'))
            days = end - start + 1
            
            if city in city_days:
                city_days[city] += days
            else:
                city_days[city] = days
        
        # Check required days
        for city, req_days in required_days.items():
            if city_days.get(city, 0) != req_days:
                return False
        
        # Check Santorini conference days
        santorini_stay = None
        for stay in itinerary:
            if stay['place'] == 'Santorini':
                santorini_stay = stay
                break
        
        if santorini_stay:
            day_range = santorini_stay['day_range']
            start, end = map(int, day_range.replace('Day ', '').split('-'))
            if not (start <= 13 and end >= 14):
                return False
        else:
            return False
        
        return True
    
    problem.addConstraint(valid_itinerary_constraint, ["visit_order"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if solutions:
        # Use the first valid solution
        order = solutions[0]["visit_order"]
        itinerary = calculate_itinerary(order)
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()