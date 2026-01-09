import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities
    cities = ['Valencia', 'Athens', 'Naples', 'Zurich']
    
    # Total days
    total_days = 20
    
    # Define variables for start day of each city stay
    # We'll model this as the start day for each city visit
    problem.addVariable('Valencia_start', range(1, total_days))
    problem.addVariable('Athens_start', range(1, total_days))
    problem.addVariable('Naples_start', range(1, total_days))
    problem.addVariable('Zurich_start', range(1, total_days))
    
    # Duration constraints
    valencia_days = 6
    athens_days = 6
    naples_days = 5
    zurich_days = 6
    
    # Flight connections
    connections = {
        'Valencia': ['Naples', 'Athens', 'Zurich'],
        'Athens': ['Valencia', 'Naples', 'Zurich'],
        'Naples': ['Valencia', 'Athens', 'Zurich'],
        'Zurich': ['Naples', 'Athens', 'Valencia']
    }
    
    # Custom constraint function
    def itinerary_constraint(val_start, ath_start, nap_start, zur_start):
        # Calculate end days
        val_end = val_start + valencia_days - 1
        ath_end = ath_start + athens_days - 1
        nap_end = nap_start + naples_days - 1
        zur_end = zur_start + zurich_days - 1
        
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
        
        # Sort by start day
        stays.sort()
        
        # Check for overlaps
        for i in range(len(stays) - 1):
            current_end = stays[i][1]
            next_start = stays[i + 1][0]
            if current_end >= next_start:
                return False
        
        # Check Athens relative constraint (between day 1 and day 6)
        if not (1 <= ath_start <= 6):
            return False
        
        # Check Naples wedding constraint (between day 16 and day 20)
        if not (16 <= nap_start <= 20 - naples_days + 1):
            return False
        
        # Check flight connections between consecutive cities
        for i in range(len(stays) - 1):
            current_city = stays[i][2]
            next_city = stays[i + 1][2]
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
    val_start = solution['Valencia_start']
    ath_start = solution['Athens_start']
    nap_start = solution['Naples_start']
    zur_start = solution['Zurich_start']
    
    stays = [
        (val_start, val_start + valencia_days - 1, 'Valencia'),
        (ath_start, ath_start + athens_days - 1, 'Athens'),
        (nap_start, nap_start + naples_days - 1, 'Naples'),
        (zur_start, zur_start + zurich_days - 1, 'Zurich')
    ]
    
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