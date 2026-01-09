import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes
    travel_times = {
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Russian Hill'): 4,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Russian Hill'): 13,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Union Square'): 11
    }
    
    # Convert times to minutes since 9:00 AM
    start_of_day = datetime.strptime('9:00', '%H:%M')
    emily_window_start = (datetime.strptime('16:00', '%H:%M') - start_of_day).total_seconds() / 60
    emily_window_end = (datetime.strptime('17:15', '%H:%M') - start_of_day).total_seconds() / 60
    margaret_window_start = (datetime.strptime('19:00', '%H:%M') - start_of_day).total_seconds() / 60
    margaret_window_end = (datetime.strptime('21:00', '%H:%M') - start_of_day).total_seconds() / 60
    
    # Meeting duration requirements
    emily_min_duration = 45
    margaret_min_duration = 120
    
    problem = constraint.Problem()
    
    # Variables: start times and durations for each meeting
    # emily_start: when we start meeting Emily (within her window)
    # emily_duration: how long we meet Emily (at least 45 min)
    # margaret_start: when we start meeting Margaret (within her window)  
    # margaret_duration: how long we meet Margaret (at least 120 min)
    
    # Emily's meeting must be within her availability
    problem.addVariable('emily_start', range(int(emily_window_start), int(emily_window_end - emily_min_duration) + 1))
    problem.addVariable('emily_duration', range(emily_min_duration, int(emily_window_end - emily_window_start) + 1))
    
    # Margaret's meeting must be within her availability
    problem.addVariable('margaret_start', range(int(margaret_window_start), int(margaret_window_end - margaret_min_duration) + 1))
    problem.addVariable('margaret_duration', range(margaret_min_duration, int(margaret_window_end - margaret_window_start) + 1))
    
    # Constraint: Emily meeting must end within her window
    def emily_time_constraint(start, duration):
        return start + duration <= emily_window_end
    
    # Constraint: Margaret meeting must end within her window  
    def margaret_time_constraint(start, duration):
        return start + duration <= margaret_window_end
    
    # Constraint: Travel time between meetings
    def travel_constraint(emily_start, emily_duration, margaret_start, margaret_duration):
        emily_end = emily_start + emily_duration
        margaret_end = margaret_start + margaret_duration
        
        # We start at North Beach, go to Union Square to meet Emily, then to Russian Hill to meet Margaret
        travel_to_emily = travel_times[('North Beach', 'Union Square')]
        travel_to_margaret = travel_times[('Union Square', 'Russian Hill')]
        
        # Must have enough time to travel from start location to Emily
        if emily_start < travel_to_emily:
            return False
            
        # Must have enough time to travel from Emily to Margaret
        time_after_emily = margaret_start - emily_end
        if time_after_emily < travel_to_margaret:
            return False
            
        return True
    
    problem.addConstraint(emily_time_constraint, ['emily_start', 'emily_duration'])
    problem.addConstraint(margaret_time_constraint, ['margaret_start', 'margaret_duration'])
    problem.addConstraint(travel_constraint, ['emily_start', 'emily_duration', 'margaret_start', 'margaret_duration'])
    
    # Objective: maximize total meeting time
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution with both meetings, try just one meeting
        best_solution = None
        max_duration = 0
        
        # Try Emily only
        emily_problem = constraint.Problem()
        emily_problem.addVariable('emily_start', range(int(emily_window_start), int(emily_window_end - emily_min_duration) + 1))
        emily_problem.addVariable('emily_duration', range(emily_min_duration, int(emily_window_end - emily_window_start) + 1))
        emily_problem.addConstraint(emily_time_constraint, ['emily_start', 'emily_duration'])
        
        emily_solutions = emily_problem.getSolutions()
        for sol in emily_solutions:
            total_time = sol['emily_duration']
            if total_time > max_duration:
                max_duration = total_time
                best_solution = {'emily_start': sol['emily_start'], 'emily_duration': sol['emily_duration']}
        
        # Try Margaret only
        margaret_problem = constraint.Problem()
        margaret_problem.addVariable('margaret_start', range(int(margaret_window_start), int(margaret_window_end - margaret_min_duration) + 1))
        margaret_problem.addVariable('margaret_duration', range(margaret_min_duration, int(margaret_window_end - margaret_window_start) + 1))
        margaret_problem.addConstraint(margaret_time_constraint, ['margaret_start', 'margaret_duration'])
        
        margaret_solutions = margaret_problem.getSolutions()
        for sol in margaret_solutions:
            total_time = sol['margaret_duration']
            if total_time > max_duration:
                max_duration = total_time
                best_solution = {'margaret_start': sol['margaret_start'], 'margaret_duration': sol['margaret_duration']}
        
        if best_solution:
            solutions = [best_solution]
        else:
            solutions = []
    
    if solutions:
        # Find solution with maximum total meeting time
        best_solution = None
        max_total_time = -1
        
        for sol in solutions:
            total_time = 0
            if 'emily_duration' in sol:
                total_time += sol['emily_duration']
            if 'margaret_duration' in sol:
                total_time += sol['margaret_duration']
            
            if total_time > max_total_time:
                max_total_time = total_time
                best_solution = sol
        
        # Build itinerary
        itinerary = []
        
        if 'emily_start' in best_solution:
            emily_start_time = start_of_day + timedelta(minutes=best_solution['emily_start'])
            emily_end_time = emily_start_time + timedelta(minutes=best_solution['emily_duration'])
            
            itinerary.append({
                "action": "meet",
                "location": "Union Square",
                "person": "Emily",
                "start_time": emily_start_time.strftime('%H:%M'),
                "end_time": emily_end_time.strftime('%H:%M')
            })
        
        if 'margaret_start' in best_solution:
            margaret_start_time = start_of_day + timedelta(minutes=best_solution['margaret_start'])
            margaret_end_time = margaret_start_time + timedelta(minutes=best_solution['margaret_duration'])
            
            itinerary.append({
                "action": "meet",
                "location": "Russian Hill",
                "person": "Margaret",
                "start_time": margaret_start_time.strftime('%H:%M'),
                "end_time": margaret_end_time.strftime('%H:%M')
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()