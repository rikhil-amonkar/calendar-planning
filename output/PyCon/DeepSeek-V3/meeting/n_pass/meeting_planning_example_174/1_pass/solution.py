import constraint
import json

def main():
    # Travel times in minutes
    travel_times = {
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Mission District'): 13,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Mission District'): 15,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Pacific Heights'): 16
    }
    
    # Convert all times to minutes since 9:00 AM
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = map(int, time_str.split(':'))
            return hours * 60 + minutes
        else:
            # Handle AM/PM format
            time_str = time_str.upper()
            if 'AM' in time_str:
                time_str = time_str.replace('AM', '').strip()
                hours, minutes = map(int, time_str.split(':'))
                if hours == 12:
                    hours = 0
                return hours * 60 + minutes
            else:  # PM
                time_str = time_str.replace('PM', '').strip()
                hours, minutes = map(int, time_str.split(':'))
                if hours != 12:
                    hours += 12
                return hours * 60 + minutes
    
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Convert constraints to minutes since 9:00 AM
    start_time_nob_hill = time_to_minutes('9:00')
    thomas_start = time_to_minutes('3:30 PM')
    thomas_end = time_to_minutes('7:15 PM')
    kenneth_start = time_to_minutes('12:00 PM')
    kenneth_end = time_to_minutes('3:45 PM')
    
    thomas_min_duration = 75
    kenneth_min_duration = 45
    
    problem = constraint.Problem()
    
    # Variables: start times for each meeting
    # We'll have two possible meetings: one with Kenneth and one with Thomas
    # Let's define variables for the start time of each meeting
    
    # Kenneth meeting at Mission District
    problem.addVariable('kenneth_start', range(kenneth_start, kenneth_end - kenneth_min_duration + 1))
    problem.addVariable('kenneth_duration', [kenneth_min_duration])
    
    # Thomas meeting at Pacific Heights  
    problem.addVariable('thomas_start', range(thomas_start, thomas_end - thomas_min_duration + 1))
    problem.addVariable('thomas_duration', [thomas_min_duration])
    
    # Add variable for which meeting to do first
    problem.addVariable('order', [0, 1])  # 0 = Kenneth first, 1 = Thomas first
    
    def travel_constraint(k_start, k_dur, t_start, t_dur, order):
        k_end = k_start + k_dur
        t_end = t_start + t_dur
        
        if order == 0:  # Kenneth first, then Thomas
            # Travel from Mission District to Pacific Heights
            travel_time = travel_times[('Mission District', 'Pacific Heights')]
            if k_end + travel_time > t_start:
                return False
        else:  # Thomas first, then Kenneth
            # Travel from Pacific Heights to Mission District
            travel_time = travel_times[('Pacific Heights', 'Mission District')]
            if t_end + travel_time > k_start:
                return False
        
        # Check if we can make it from Nob Hill to first meeting
        if order == 0:  # Kenneth first
            travel_to_first = travel_times[('Nob Hill', 'Mission District')]
            if start_time_nob_hill + travel_to_first > k_start:
                return False
        else:  # Thomas first
            travel_to_first = travel_times[('Nob Hill', 'Pacific Heights')]
            if start_time_nob_hill + travel_to_first > t_start:
                return False
        
        return True
    
    problem.addConstraint(travel_constraint, 
                         ['kenneth_start', 'kenneth_duration', 
                          'thomas_start', 'thomas_duration', 'order'])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Try single meeting solutions if no two-meeting solution exists
        single_meeting_solutions = []
        
        # Try meeting only Kenneth
        kenneth_solutions = []
        for k_start in range(kenneth_start, kenneth_end - kenneth_min_duration + 1):
            travel_time = travel_times[('Nob Hill', 'Mission District')]
            if start_time_nob_hill + travel_time <= k_start:
                kenneth_solutions.append({
                    'kenneth_start': k_start,
                    'kenneth_duration': kenneth_min_duration,
                    'thomas_start': None,
                    'thomas_duration': 0,
                    'order': 0
                })
        
        # Try meeting only Thomas
        thomas_solutions = []
        for t_start in range(thomas_start, thomas_end - thomas_min_duration + 1):
            travel_time = travel_times[('Nob Hill', 'Pacific Heights')]
            if start_time_nob_hill + travel_time <= t_start:
                thomas_solutions.append({
                    'kenneth_start': None,
                    'kenneth_duration': 0,
                    'thomas_start': t_start,
                    'thomas_duration': thomas_min_duration,
                    'order': 1
                })
        
        # Choose the solution with the most meeting time
        best_solution = None
        max_duration = -1
        
        for sol in kenneth_solutions:
            duration = sol['kenneth_duration']
            if duration > max_duration:
                max_duration = duration
                best_solution = sol
        
        for sol in thomas_solutions:
            duration = sol['thomas_duration']
            if duration > max_duration:
                max_duration = duration
                best_solution = sol
        
        solutions = [best_solution] if best_solution else []
    
    if solutions:
        # For simplicity, take the first valid solution
        # In a real scenario, you might want to optimize further
        solution = solutions[0]
        
        itinerary = []
        
        if solution['order'] == 0:  # Kenneth first
            if solution['kenneth_start'] is not None:
                k_start_time = minutes_to_time(solution['kenneth_start'])
                k_end_time = minutes_to_time(solution['kenneth_start'] + solution['kenneth_duration'])
                itinerary.append({
                    "action": "meet",
                    "location": "Mission District", 
                    "person": "Kenneth",
                    "start_time": k_start_time,
                    "end_time": k_end_time
                })
            
            if solution['thomas_start'] is not None:
                t_start_time = minutes_to_time(solution['thomas_start'])
                t_end_time = minutes_to_time(solution['thomas_start'] + solution['thomas_duration'])
                itinerary.append({
                    "action": "meet",
                    "location": "Pacific Heights",
                    "person": "Thomas", 
                    "start_time": t_start_time,
                    "end_time": t_end_time
                })
        else:  # Thomas first
            if solution['thomas_start'] is not None:
                t_start_time = minutes_to_time(solution['thomas_start'])
                t_end_time = minutes_to_time(solution['thomas_start'] + solution['thomas_duration'])
                itinerary.append({
                    "action": "meet",
                    "location": "Pacific Heights",
                    "person": "Thomas",
                    "start_time": t_start_time,
                    "end_time": t_end_time
                })
            
            if solution['kenneth_start'] is not None:
                k_start_time = minutes_to_time(solution['kenneth_start'])
                k_end_time = minutes_to_time(solution['kenneth_start'] + solution['kenneth_duration'])
                itinerary.append({
                    "action": "meet", 
                    "location": "Mission District",
                    "person": "Kenneth",
                    "start_time": k_start_time,
                    "end_time": k_end_time
                })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()