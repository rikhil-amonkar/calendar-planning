import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes
    travel_times = {
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'Chinatown'): 20,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Chinatown'): 16,
        ('Union Square', 'The Castro'): 19,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Union Square'): 7
    }
    
    # Convert all times to minutes since 9:00 AM
    start_of_day = datetime.strptime('9:00', '%H:%M')
    
    # Friend constraints (in minutes since 9:00 AM)
    emily_start = (datetime.strptime('11:45', '%H:%M') - start_of_day).total_seconds() // 60
    emily_end = (datetime.strptime('15:15', '%H:%M') - start_of_day).total_seconds() // 60
    barbara_start = (datetime.strptime('16:45', '%H:%M') - start_of_day).total_seconds() // 60
    barbara_end = (datetime.strptime('18:15', '%H:%M') - start_of_day).total_seconds() // 60
    william_start = (datetime.strptime('17:15', '%H:%M') - start_of_day).total_seconds() // 60
    william_end = (datetime.strptime('19:00', '%H:%M') - start_of_day).total_seconds() // 60
    
    # Minimum meeting durations
    emily_min = 105
    barbara_min = 60
    william_min = 105
    
    problem = constraint.Problem()
    
    # Variables: start times for each meeting
    # Emily at Alamo Square
    problem.addVariable('emily_start', range(int(emily_start), int(emily_end - emily_min + 1)))
    problem.addVariable('emily_duration', [emily_min])
    
    # Barbara at Union Square
    problem.addVariable('barbara_start', range(int(barbara_start), int(barbara_end - barbara_min + 1)))
    problem.addVariable('barbara_duration', [barbara_min])
    
    # William at Chinatown
    problem.addVariable('william_start', range(int(william_start), int(william_end - william_min + 1)))
    problem.addVariable('william_duration', [william_min])
    
    # Constraints for travel times between meetings
    def travel_constraint(emily_s, barbara_s, william_s, emily_d, barbara_d, william_d):
        emily_end = emily_s + emily_d
        barbara_end = barbara_s + barbara_d
        william_end = william_s + william_d
        
        # Check all possible orders and ensure travel time is accounted for
        orders = [
            # Emily -> Barbara -> William
            (emily_end + travel_times[('Alamo Square', 'Union Square')] <= barbara_s and
             barbara_end + travel_times[('Union Square', 'Chinatown')] <= william_s),
            
            # Emily -> William -> Barbara
            (emily_end + travel_times[('Alamo Square', 'Chinatown')] <= william_s and
             william_end + travel_times[('Chinatown', 'Union Square')] <= barbara_s),
            
            # Barbara -> Emily -> William
            (barbara_end + travel_times[('Union Square', 'Alamo Square')] <= emily_s and
             emily_end + travel_times[('Alamo Square', 'Chinatown')] <= william_s),
            
            # Barbara -> William -> Emily
            (barbara_end + travel_times[('Union Square', 'Chinatown')] <= william_s and
             william_end + travel_times[('Chinatown', 'Alamo Square')] <= emily_s),
            
            # William -> Emily -> Barbara
            (william_end + travel_times[('Chinatown', 'Alamo Square')] <= emily_s and
             emily_end + travel_times[('Alamo Square', 'Union Square')] <= barbara_s),
            
            # William -> Barbara -> Emily
            (william_end + travel_times[('Chinatown', 'Union Square')] <= barbara_s and
             barbara_end + travel_times[('Union Square', 'Alamo Square')] <= emily_s)
        ]
        
        return any(orders)
    
    problem.addConstraint(travel_constraint, 
                         ['emily_start', 'barbara_start', 'william_start', 
                          'emily_duration', 'barbara_duration', 'william_duration'])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with all three, try with two meetings
        best_solution = None
        best_meeting_count = 0
        best_total_time = 0
        
        # Try all combinations of two meetings
        for combo in [('emily', 'barbara'), ('emily', 'william'), ('barbara', 'william')]:
            problem2 = constraint.Problem()
            
            if 'emily' in combo:
                problem2.addVariable('emily_start', range(int(emily_start), int(emily_end - emily_min + 1)))
                problem2.addVariable('emily_duration', [emily_min])
            if 'barbara' in combo:
                problem2.addVariable('barbara_start', range(int(barbara_start), int(barbara_end - barbara_min + 1)))
                problem2.addVariable('barbara_duration', [barbara_min])
            if 'william' in combo:
                problem2.addVariable('william_start', range(int(william_start), int(william_end - william_min + 1)))
                problem2.addVariable('william_duration', [william_min])
            
            def two_meeting_constraint(*args):
                if combo == ('emily', 'barbara'):
                    emily_s, barbara_s, emily_d, barbara_d = args
                    emily_end = emily_s + emily_d
                    return (emily_end + travel_times[('Alamo Square', 'Union Square')] <= barbara_s or
                           barbara_s + barbara_d + travel_times[('Union Square', 'Alamo Square')] <= emily_s)
                elif combo == ('emily', 'william'):
                    emily_s, william_s, emily_d, william_d = args
                    emily_end = emily_s + emily_d
                    return (emily_end + travel_times[('Alamo Square', 'Chinatown')] <= william_s or
                           william_s + william_d + travel_times[('Chinatown', 'Alamo Square')] <= emily_s)
                elif combo == ('barbara', 'william'):
                    barbara_s, william_s, barbara_d, william_d = args
                    barbara_end = barbara_s + barbara_d
                    return (barbara_end + travel_times[('Union Square', 'Chinatown')] <= william_s or
                           william_s + william_d + travel_times[('Chinatown', 'Union Square')] <= barbara_s)
            
            if combo == ('emily', 'barbara'):
                problem2.addConstraint(two_meeting_constraint, 
                                     ['emily_start', 'barbara_start', 'emily_duration', 'barbara_duration'])
            elif combo == ('emily', 'william'):
                problem2.addConstraint(two_meeting_constraint, 
                                     ['emily_start', 'william_start', 'emily_duration', 'william_duration'])
            elif combo == ('barbara', 'william'):
                problem2.addConstraint(two_meeting_constraint, 
                                     ['barbara_start', 'william_start', 'barbara_duration', 'william_duration'])
            
            solutions2 = problem2.getSolutions()
            if solutions2:
                meeting_count = 2
                for sol in solutions2:
                    total_time = 0
                    if 'emily' in combo:
                        total_time += emily_min
                    if 'barbara' in combo:
                        total_time += barbara_min
                    if 'william' in combo:
                        total_time += william_min
                    
                    if (meeting_count > best_meeting_count or 
                        (meeting_count == best_meeting_count and total_time > best_total_time)):
                        best_meeting_count = meeting_count
                        best_total_time = total_time
                        best_solution = sol
                        best_solution['combo'] = combo
        
        if best_solution:
            solutions = [best_solution]
        else:
            # Try with just one meeting
            best_solution = None
            best_duration = 0
            
            for person, (start_time, end_time, min_duration, location) in [
                ('emily', (emily_start, emily_end, emily_min, 'Alamo Square')),
                ('barbara', (barbara_start, barbara_end, barbara_min, 'Union Square')),
                ('william', (william_start, william_end, william_min, 'Chinatown'))
            ]:
                if start_time + min_duration <= end_time:
                    if min_duration > best_duration:
                        best_duration = min_duration
                        best_solution = {
                            f'{person}_start': start_time,
                            f'{person}_duration': min_duration,
                            'single_person': person,
                            'location': location
                        }
            
            if best_solution:
                solutions = [best_solution]
            else:
                solutions = []
    
    if solutions:
        # Use the first valid solution
        solution = solutions[0]
        
        itinerary = []
        
        # Helper function to convert minutes to time string
        def minutes_to_time(minutes):
            base_time = start_of_day + timedelta(minutes=minutes)
            return base_time.strftime('%H:%M').lstrip('0')
        
        # Determine the order of meetings
        if 'combo' in solution:
            # Two meetings case
            combo = solution['combo']
            meetings = []
            for person in combo:
                start = solution[f'{person}_start']
                duration = solution[f'{person}_duration']
                if person == 'emily':
                    location = 'Alamo Square'
                elif person == 'barbara':
                    location = 'Union Square'
                else:  # william
                    location = 'Chinatown'
                meetings.append((start, duration, location, person))
            
            # Sort by start time
            meetings.sort()
            
            for start, duration, location, person in meetings:
                end = start + duration
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person.capitalize(),
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        elif 'single_person' in solution:
            # Single meeting case
            person = solution['single_person']
            start = solution[f'{person}_start']
            duration = solution[f'{person}_duration']
            location = solution['location']
            
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person.capitalize(),
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(start + duration)
            })
        else:
            # Three meetings case - determine order
            meetings = [
                (solution['emily_start'], solution['emily_duration'], 'Alamo Square', 'Emily'),
                (solution['barbara_start'], solution['barbara_duration'], 'Union Square', 'Barbara'),
                (solution['william_start'], solution['william_duration'], 'Chinatown', 'William')
            ]
            
            # Sort by start time
            meetings.sort()
            
            for start, duration, location, person in meetings:
                end = start + duration
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()