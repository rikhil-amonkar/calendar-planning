import constraint
import json
from datetime import datetime, timedelta

def main():
    # Travel times in minutes
    travel_times = {
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Presidio'): 31,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Presidio'): 24,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Union Square'): 22
    }
    
    # Convert times to minutes since 9:00 AM
    start_time_base = datetime.strptime('9:00', '%H:%M')
    
    # Friend constraints (in minutes since 9:00 AM)
    richard_start = (datetime.strptime('8:45', '%H:%M') - start_time_base).total_seconds() / 60
    richard_end = (datetime.strptime('13:00', '%H:%M') - start_time_base).total_seconds() / 60
    
    charles_start = (datetime.strptime('9:45', '%H:%M') - start_time_base).total_seconds() / 60
    charles_end = (datetime.strptime('13:00', '%H:%M') - start_time_base).total_seconds() / 60
    
    # Minimum meeting durations
    min_duration = 120
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start times for each meeting (in minutes since 9:00 AM)
    problem.addVariable('richard_start', range(int(richard_start), int(richard_end - min_duration) + 1))
    problem.addVariable('charles_start', range(int(charles_start), int(charles_end - min_duration) + 1))
    
    # Helper variables for meeting end times
    def richard_end_func(richard_start):
        return richard_start + min_duration
    
    def charles_end_func(charles_start):
        return charles_start + min_duration
    
    problem.addConstraint(richard_end_func, ['richard_start'])
    problem.addConstraint(charles_end_func, ['charles_start'])
    
    # Constraint: meetings must not overlap when accounting for travel
    def no_overlap(richard_start, charles_start):
        richard_end = richard_start + min_duration
        charles_end = charles_start + min_duration
        
        # Try both orders: Richard first then Charles, or Charles first then Richard
        # Richard first, then Charles
        if richard_end + travel_times[('Union Square', 'Presidio')] <= charles_start:
            return True
        
        # Charles first, then Richard  
        if charles_end + travel_times[('Presidio', 'Union Square')] <= richard_start:
            return True
            
        return False
    
    problem.addConstraint(no_overlap, ['richard_start', 'charles_start'])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution with both meetings, try with just one
        best_solution = None
        # Try Richard only
        if richard_end - max(richard_start, 0) >= min_duration:
            best_solution = {'richard_start': max(richard_start, 0), 'charles_start': None}
        # Try Charles only  
        elif charles_end - max(charles_start, 0) >= min_duration:
            best_solution = {'richard_start': None, 'charles_start': max(charles_start, 0)}
    else:
        # Find the solution that maximizes total meeting time
        best_solution = None
        max_total_time = 0
        
        for sol in solutions:
            total_time = min_duration * 2  # Both meetings
            if total_time > max_total_time:
                max_total_time = total_time
                best_solution = sol
    
    # Build itinerary
    itinerary = []
    
    def format_time(minutes):
        time_obj = start_time_base + timedelta(minutes=minutes)
        return time_obj.strftime('%H:%M').lstrip('0')
    
    if best_solution:
        if best_solution.get('richard_start') is not None:
            richard_start = best_solution['richard_start']
            richard_end = richard_start + min_duration
            itinerary.append({
                "action": "meet",
                "location": "Union Square", 
                "person": "Richard",
                "start_time": format_time(richard_start),
                "end_time": format_time(richard_end)
            })
        
        if best_solution.get('charles_start') is not None:
            charles_start = best_solution['charles_start']
            charles_end = charles_start + min_duration
            itinerary.append({
                "action": "meet",
                "location": "Presidio",
                "person": "Charles", 
                "start_time": format_time(charles_start),
                "end_time": format_time(charles_end)
            })
    
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: datetime.strptime(x['start_time'], '%H:%M'))
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()