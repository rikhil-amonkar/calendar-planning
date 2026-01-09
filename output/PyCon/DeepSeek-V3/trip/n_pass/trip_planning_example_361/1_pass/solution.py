import constraint
import json

def main():
    problem = constraint.Problem()
    
    # Define variables for start days of each city stay
    # We'll have: paris_start, madrid_start, bucharest_start, seville_start
    # And corresponding end days: paris_end, madrid_end, bucharest_end, seville_end
    
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
    
    # Calculate end days based on start days and durations
    def get_end_day(start, duration):
        return start + duration - 1
    
    # Constraint: All stays must be within the 15-day period
    def within_period(start, duration):
        return start + duration - 1 <= total_days
    
    problem.addConstraint(lambda p_start: within_period(p_start, paris_days), ['paris_start'])
    problem.addConstraint(lambda m_start: within_period(m_start, madrid_days), ['madrid_start'])
    problem.addConstraint(lambda b_start: within_period(b_start, bucharest_days), ['bucharest_start'])
    problem.addConstraint(lambda s_start: within_period(s_start, seville_days), ['seville_start'])
    
    # Constraint: No overlapping stays (cities visited sequentially)
    def no_overlap(starts, durations):
        pairs = [(starts[i], durations[i]) for i in range(len(starts))]
        pairs.sort()
        
        for i in range(len(pairs) - 1):
            current_end = pairs[i][0] + pairs[i][1] - 1
            next_start = pairs[i + 1][0]
            if current_end >= next_start:
                return False
        return True
    
    problem.addConstraint(
        lambda p, m, b, s: no_overlap([p, m, b, s], [paris_days, madrid_days, bucharest_days, seville_days]),
        ['paris_start', 'madrid_start', 'bucharest_start', 'seville_start']
    )
    
    # Special constraints from the problem description
    # Madrid must include days 1-7 for the annual show
    def madrid_includes_1_to_7(m_start):
        return m_start <= 1 and get_end_day(m_start, madrid_days) >= 7
    
    problem.addConstraint(madrid_includes_1_to_7, ['madrid_start'])
    
    # Bucharest must be between day 14 and 15
    def bucharest_in_14_15(b_start):
        return b_start <= 14 and get_end_day(b_start, bucharest_days) >= 14
    
    problem.addConstraint(bucharest_in_14_15, ['bucharest_start'])
    
    # Constraint: Direct flights between consecutive cities
    # Available direct flights: Paris-Bucharest, Seville-Paris, Madrid-Bucharest, Madrid-Paris, Madrid-Seville
    flight_routes = {
        'Paris': ['Bucharest', 'Seville', 'Madrid'],
        'Madrid': ['Bucharest', 'Paris', 'Seville'],
        'Bucharest': ['Paris', 'Madrid'],
        'Seville': ['Paris', 'Madrid']
    }
    
    def valid_flight_sequence(starts_dict):
        # Get the order of cities by start day
        cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']
        ordered = sorted([(starts_dict['paris_start'], 'Paris'),
                         (starts_dict['madrid_start'], 'Madrid'),
                         (starts_dict['bucharest_start'], 'Bucharest'),
                         (starts_dict['seville_start'], 'Seville')])
        
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
        result = {"error": "No valid itinerary found"}
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