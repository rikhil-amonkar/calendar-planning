import json
from constraint import Problem

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities and their durations
    cities = ['Valencia', 'Athens', 'Naples', 'Zurich']
    durations = {
        'Valencia': 6,
        'Athens': 6,
        'Naples': 5,
        'Zurich': 6
    }
    
    total_days = 20
    
    # Define variables for start day of each city stay
    # Use wider ranges to allow more flexibility
    problem.addVariable('Athens_start', range(1, 7))  # Athens must start between day 1-6
    problem.addVariable('Naples_start', range(12, 17))  # Naples must end between day 16-20, so start between 12-16
    problem.addVariable('Valencia_start', range(1, total_days + 1))
    problem.addVariable('Zurich_start', range(1, total_days + 1))
    
    def itinerary_constraint(val_start, ath_start, nap_start, zur_start):
        # Calculate end days
        val_end = val_start + durations['Valencia'] - 1
        ath_end = ath_start + durations['Athens'] - 1
        nap_end = nap_start + durations['Naples'] - 1
        zur_end = zur_start + durations['Zurich'] - 1
        
        # Check if all stays fit within 20 days
        if max(val_end, ath_end, nap_end, zur_end) > total_days:
            return False
        
        # Check for overlaps - no two cities can be visited simultaneously
        stays = [
            (val_start, val_end, 'Valencia'),
            (ath_start, ath_end, 'Athens'),
            (nap_start, nap_end, 'Naples'),
            (zur_start, zur_end, 'Zurich')
        ]
        
        # Check for overlaps
        for i in range(len(stays)):
            for j in range(i + 1, len(stays)):
                start_i, end_i, city_i = stays[i]
                start_j, end_j, city_j = stays[j]
                # Check if the two stays overlap
                if not (end_i < start_j or end_j < start_i):
                    return False
        
        # Check Athens constraint (already enforced by variable domain)
        # Check Naples wedding constraint
        if not (16 <= nap_end <= 20):
            return False
        
        # Check flight connections - all cities must be connected to at least one other city
        # We'll use the provided flight connections
        connections = {
            'Valencia': ['Naples', 'Athens', 'Zurich'],
            'Athens': ['Valencia', 'Naples', 'Zurich'],
            'Naples': ['Valencia', 'Athens', 'Zurich'],
            'Zurich': ['Naples', 'Athens', 'Valencia']
        }
        
        # Create a graph of the itinerary order
        ordered_stays = sorted(stays, key=lambda x: x[0])
        
        # Check connections between consecutive cities in the itinerary
        # Allow for travel days between stays
        for i in range(len(ordered_stays) - 1):
            current_city = ordered_stays[i][2]
            next_city = ordered_stays[i + 1][2]
            if next_city not in connections[current_city]:
                return False
        
        return True
    
    problem.addConstraint(itinerary_constraint, 
                         ['Valencia_start', 'Athens_start', 'Naples_start', 'Zurich_start'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Build the itinerary
    stays = []
    for city in cities:
        start = solution[f'{city}_start']
        end = start + durations[city] - 1
        stays.append((start, end, city))
    
    # Sort by start day
    stays.sort()
    
    # Create itinerary in required format
    itinerary = []
    for start, end, city in stays:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))