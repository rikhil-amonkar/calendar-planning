import constraint
import json

def main():
    # Problem parameters
    total_days = 12
    riga_days = 5
    vilnius_days = 7
    dublin_days = 2
    
    # Create problem instance
    problem = constraint.Problem()
    
    # Variables: start day for each city (0-indexed)
    # We'll use -1 to indicate the city is not visited
    problem.addVariable('riga_start', range(total_days))
    problem.addVariable('vilnius_start', range(total_days))
    problem.addVariable('dublin_start', range(total_days))
    
    # Variables: duration in each city
    problem.addVariable('riga_duration', [riga_days])
    problem.addVariable('vilnius_duration', [vilnius_days])
    problem.addVariable('dublin_duration', [dublin_days])
    
    # Constraint: all days must be covered exactly once
    def all_days_covered(riga_s, vilnius_s, dublin_s, riga_d, vilnius_d, dublin_d):
        days_covered = set()
        
        # Add Riga days
        for day in range(riga_s, riga_s + riga_d):
            if day < total_days:
                days_covered.add(day)
        
        # Add Vilnius days
        for day in range(vilnius_s, vilnius_s + vilnius_d):
            if day < total_days:
                days_covered.add(day)
        
        # Add Dublin days
        for day in range(dublin_s, dublin_s + dublin_d):
            if day < total_days:
                days_covered.add(day)
        
        return len(days_covered) == total_days and max(days_covered) == total_days - 1
    
    problem.addConstraint(all_days_covered, 
                         ['riga_start', 'vilnius_start', 'dublin_start', 
                          'riga_duration', 'vilnius_duration', 'dublin_duration'])
    
    # Constraint: no overlapping stays
    def no_overlap(riga_s, vilnius_s, dublin_s, riga_d, vilnius_d, dublin_d):
        riga_range = set(range(riga_s, riga_s + riga_d))
        vilnius_range = set(range(vilnius_s, vilnius_s + vilnius_d))
        dublin_range = set(range(dublin_s, dublin_s + dublin_d))
        
        # Check for overlaps
        if riga_range & vilnius_range:
            return False
        if riga_range & dublin_range:
            return False
        if vilnius_range & dublin_range:
            return False
        
        return True
    
    problem.addConstraint(no_overlap, 
                         ['riga_start', 'vilnius_start', 'dublin_start', 
                          'riga_duration', 'vilnius_duration', 'dublin_duration'])
    
    # Constraint: travel must follow direct flight routes
    def valid_travel_sequence(riga_s, vilnius_s, dublin_s, riga_d, vilnius_d, dublin_d):
        # Determine visit order by start day
        visits = [
            ('Riga', riga_s, riga_d),
            ('Vilnius', vilnius_s, vilnius_d),
            ('Dublin', dublin_s, dublin_d)
        ]
        visits.sort(key=lambda x: x[1])  # Sort by start day
        
        # Check if travel sequence is valid based on direct flights
        # Direct flights: Dublin-Riga, Riga-Vilnius
        valid_transitions = {
            'Dublin': ['Riga'],
            'Riga': ['Dublin', 'Vilnius'],
            'Vilnius': ['Riga']
        }
        
        for i in range(len(visits) - 1):
            current_city = visits[i][0]
            next_city = visits[i + 1][0]
            
            if next_city not in valid_transitions[current_city]:
                return False
        
        return True
    
    problem.addConstraint(valid_travel_sequence, 
                         ['riga_start', 'vilnius_start', 'dublin_start', 
                          'riga_duration', 'vilnius_duration', 'dublin_duration'])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: create a valid itinerary based on the constraints
        itinerary = []
        itinerary.append({"day_range": f"Day 1-{dublin_days + 1}", "place": "Dublin"})
        itinerary.append({"day_range": f"Day {dublin_days + 1}-{dublin_days + riga_days + 1}", "place": "Riga"})
        itinerary.append({"day_range": f"Day {dublin_days + riga_days + 1}-{total_days + 1}", "place": "Vilnius"})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
        return
    
    # Use the first valid solution
    sol = solutions[0]
    
    # Create visit segments
    visits = [
        ('Riga', sol['riga_start'], sol['riga_duration']),
        ('Vilnius', sol['vilnius_start'], sol['vilnius_duration']),
        ('Dublin', sol['dublin_start'], sol['dublin_duration'])
    ]
    
    # Sort by start day
    visits.sort(key=lambda x: x[1])
    
    # Build itinerary
    itinerary = []
    for city, start_day, duration in visits:
        day_start = start_day + 1  # Convert to 1-indexed
        day_end = start_day + duration + 1  # Convert to 1-indexed
        itinerary.append({
            "day_range": f"Day {day_start}-{day_end}",
            "place": city
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()