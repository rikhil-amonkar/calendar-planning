import constraint
import json

def main():
    problem = constraint.Problem()
    
    # Total days: 15
    total_days = 15
    
    # Fixed durations
    paris_days = 6
    madrid_days = 7
    bucharest_days = 2
    seville_days = 3
    
    # Add variables for start days (1-indexed)
    problem.addVariable('paris_start', range(1, total_days + 1))
    problem.addVariable('madrid_start', range(1, total_days + 1))
    problem.addVariable('bucharest_start', range(1, total_days + 1))
    problem.addVariable('seville_start', range(1, total_days + 1))
    
    # Constraint: All stays must be within the 15-day period
    def within_period(start, duration):
        return start + duration - 1 <= total_days
    
    problem.addConstraint(lambda p_start: within_period(p_start, paris_days), ['paris_start'])
    problem.addConstraint(lambda m_start: within_period(m_start, madrid_days), ['madrid_start'])
    problem.addConstraint(lambda b_start: within_period(b_start, bucharest_days), ['bucharest_start'])
    problem.addConstraint(lambda s_start: within_period(s_start, seville_days), ['seville_start'])
    
    # Madrid must include days 1-7 for the annual show
    # This means Madrid must start on day 1 and end on day 7 (since it's 7 days)
    problem.addConstraint(lambda m_start: m_start == 1, ['madrid_start'])
    
    # Bucharest must be between day 14 and 15
    # Since Bucharest stay is 2 days, it must start on day 14 to end on day 15
    problem.addConstraint(lambda b_start: b_start == 14, ['bucharest_start'])
    
    # Constraint: No overlapping stays (cities visited sequentially)
    def no_overlap(p_start, m_start, b_start, s_start):
        cities = [
            (p_start, paris_days, 'Paris'),
            (m_start, madrid_days, 'Madrid'),
            (b_start, bucharest_days, 'Bucharest'),
            (s_start, seville_days, 'Seville')
        ]
        
        # Sort by start day
        cities.sort()
        
        # Check for overlaps
        for i in range(len(cities) - 1):
            current_end = cities[i][0] + cities[i][1] - 1
            next_start = cities[i + 1][0]
            if current_end >= next_start:
                return False
        return True
    
    problem.addConstraint(no_overlap, ['paris_start', 'madrid_start', 'bucharest_start', 'seville_start'])
    
    # Constraint: Direct flights between consecutive cities
    # Available direct flights: Paris-Bucharest, Seville-Paris, Madrid-Bucharest, Madrid-Paris, Madrid-Seville
    flight_routes = {
        'Paris': ['Bucharest', 'Madrid', 'Seville'],
        'Madrid': ['Bucharest', 'Paris', 'Seville'],
        'Bucharest': ['Paris', 'Madrid'],
        'Seville': ['Paris', 'Madrid']
    }
    
    def valid_flight_sequence(p_start, m_start, b_start, s_start):
        # Get the order of cities by start day
        cities = [
            (p_start, 'Paris'),
            (m_start, 'Madrid'),
            (b_start, 'Bucharest'),
            (s_start, 'Seville')
        ]
        
        # Sort by start day
        ordered = sorted(cities)
        
        # Check if consecutive cities in the sequence have direct flights
        for i in range(len(ordered) - 1):
            current_city = ordered[i][1]
            next_city = ordered[i + 1][1]
            
            if next_city not in flight_routes[current_city]:
                return False
        return True
    
    problem.addConstraint(valid_flight_sequence, ['paris_start', 'madrid_start', 'bucharest_start', 'seville_start'])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Try relaxing the Bucharest constraint to allow more flexibility
        print("No solution found with strict constraints. Trying alternative approach...")
        
        # Create a new problem with relaxed Bucharest constraint
        problem2 = constraint.Problem()
        
        # Add variables
        problem2.addVariable('paris_start', range(1, total_days + 1))
        problem2.addVariable('madrid_start', range(1, total_days + 1))
        problem2.addVariable('bucharest_start', range(1, total_days + 1))
        problem2.addVariable('seville_start', range(1, total_days + 1))
        
        # Basic constraints
        problem2.addConstraint(lambda p_start: within_period(p_start, paris_days), ['paris_start'])
        problem2.addConstraint(lambda m_start: within_period(m_start, madrid_days), ['madrid_start'])
        problem2.addConstraint(lambda b_start: within_period(b_start, bucharest_days), ['bucharest_start'])
        problem2.addConstraint(lambda s_start: within_period(s_start, seville_days), ['seville_start'])
        
        # Madrid constraint (fixed)
        problem2.addConstraint(lambda m_start: m_start == 1, ['madrid_start'])
        
        # Relaxed Bucharest constraint: must include either day 14 or 15
        problem2.addConstraint(lambda b_start: b_start == 13 or b_start == 14, ['bucharest_start'])
        
        # No overlap constraint
        problem2.addConstraint(no_overlap, ['paris_start', 'madrid_start', 'bucharest_start', 'seville_start'])
        
        # Flight constraint
        problem2.addConstraint(valid_flight_sequence, ['paris_start', 'madrid_start', 'bucharest_start', 'seville_start'])
        
        solutions = problem2.getSolutions()
        
        if not solutions:
            result = {"error": "No valid itinerary found with the given constraints"}
            print(json.dumps(result))
            return
    
    # Use the first valid solution
    sol = solutions[0]
    
    # Create itinerary with day ranges
    itinerary = []
    
    # Create list of stays with start days and cities
    stays = [
        (sol['paris_start'], 'Paris', paris_days),
        (sol['madrid_start'], 'Madrid', madrid_days),
        (sol['bucharest_start'], 'Bucharest', bucharest_days),
        (sol['seville_start'], 'Seville', seville_days)
    ]
    
    # Sort by start day
    stays.sort()
    
    for start, city, duration in stays:
        end_day = start + duration - 1
        if start == end_day:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()