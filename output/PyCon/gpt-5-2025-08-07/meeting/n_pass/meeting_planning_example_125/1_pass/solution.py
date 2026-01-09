import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define travel times in minutes
    travel_times = {
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Alamo Square'): 17,
        ('Alamo Square', 'Embarcadero'): 17,
        ('Alamo Square', 'Financial District'): 17
    }
    
    # Convert all times to minutes since 9:00 (arrival time)
    start_time_ref = datetime.strptime('9:00', '%H:%M')
    
    # Stephanie's availability (Financial District)
    stephanie_start = (datetime.strptime('8:15', '%H:%M') - start_time_ref).total_seconds() / 60
    stephanie_end = (datetime.strptime('11:30', '%H:%M') - start_time_ref).total_seconds() / 60
    
    # John's availability (Alamo Square)
    john_start = (datetime.strptime('10:15', '%H:%M') - start_time_ref).total_seconds() / 60
    john_end = (datetime.strptime('20:45', '%H:%M') - start_time_ref).total_seconds() / 60
    
    # Minimum meeting durations
    stephanie_min_duration = 90
    john_min_duration = 30
    
    # Travel times
    emb_to_fin = travel_times[('Embarcadero', 'Financial District')]
    emb_to_alamo = travel_times[('Embarcadero', 'Alamo Square')]
    fin_to_alamo = travel_times[('Financial District', 'Alamo Square')]
    alamo_to_fin = travel_times[('Alamo Square', 'Financial District')]
    
    problem = constraint.Problem()
    
    # Define variables for meeting start times and durations
    # We start at Embarcadero at time 0 (9:00)
    
    # Option 1: Meet Stephanie first, then John
    problem.addVariable('stephanie_start_1', range(int(stephanie_start), int(stephanie_end - stephanie_min_duration + 1)))
    problem.addVariable('stephanie_duration_1', [stephanie_min_duration])
    problem.addVariable('john_start_1', range(int(john_start), int(john_end - john_min_duration + 1)))
    problem.addVariable('john_duration_1', [john_min_duration])
    
    # Option 2: Meet John first, then Stephanie
    problem.addVariable('john_start_2', range(int(john_start), int(john_end - john_min_duration + 1)))
    problem.addVariable('john_duration_2', [john_min_duration])
    problem.addVariable('stephanie_start_2', range(int(stephanie_start), int(stephanie_end - stephanie_min_duration + 1)))
    problem.addVariable('stephanie_duration_2', [stephanie_min_duration])
    
    # Constraints for Option 1: Stephanie first, then John
    def constraint_option1(stephanie_start, stephanie_duration, john_start, john_duration):
        stephanie_end = stephanie_start + stephanie_duration
        travel_time = fin_to_alamo
        return stephanie_end + travel_time <= john_start
    
    # Constraints for Option 2: John first, then Stephanie
    def constraint_option2(john_start, john_duration, stephanie_start, stephanie_duration):
        john_end = john_start + john_duration
        travel_time = alamo_to_fin
        return john_end + travel_time <= stephanie_start
    
    problem.addConstraint(constraint_option1, ['stephanie_start_1', 'stephanie_duration_1', 'john_start_1', 'john_duration_1'])
    problem.addConstraint(constraint_option2, ['john_start_2', 'john_duration_2', 'stephanie_start_2', 'stephanie_duration_2'])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Try meeting only one person
        problem_single = constraint.Problem()
        
        # Meet Stephanie only
        problem_single.addVariable('stephanie_start', range(int(stephanie_start), int(stephanie_end - stephanie_min_duration + 1)))
        problem_single.addVariable('stephanie_duration', [stephanie_min_duration])
        
        # Meet John only  
        problem_single.addVariable('john_start', range(int(john_start), int(john_end - john_min_duration + 1)))
        problem_single.addVariable('john_duration', [john_min_duration])
        
        single_solutions = problem_single.getSolutions()
        
        if single_solutions:
            # Choose the solution that maximizes total meeting time
            best_solution = None
            max_duration = 0
            
            for sol in single_solutions:
                if 'stephanie_start' in sol:
                    duration = stephanie_min_duration
                    if duration > max_duration:
                        max_duration = duration
                        best_solution = sol
                elif 'john_start' in sol:
                    duration = john_min_duration
                    if duration > max_duration:
                        max_duration = duration
                        best_solution = sol
            
            if best_solution:
                itinerary = []
                if 'stephanie_start' in best_solution:
                    start_time = start_time_ref + timedelta(minutes=best_solution['stephanie_start'])
                    end_time = start_time + timedelta(minutes=stephanie_min_duration)
                    itinerary.append({
                        "action": "meet",
                        "location": "Financial District",
                        "person": "Stephanie",
                        "start_time": start_time.strftime('%-H:%M'),
                        "end_time": end_time.strftime('%-H:%M')
                    })
                elif 'john_start' in best_solution:
                    start_time = start_time_ref + timedelta(minutes=best_solution['john_start'])
                    end_time = start_time + timedelta(minutes=john_min_duration)
                    itinerary.append({
                        "action": "meet",
                        "location": "Alamo Square",
                        "person": "John",
                        "start_time": start_time.strftime('%-H:%M'),
                        "end_time": end_time.strftime('%-H:%M')
                    })
                
                result = {"itinerary": itinerary}
                print(json.dumps(result, indent=2))
                return
        
        # If no solutions found at all
        result = {"itinerary": []}
        print(json.dumps(result, indent=2))
        return
    
    # Find the best solution (prefer meeting both people)
    best_solution = None
    max_total_duration = 0
    
    for sol in solutions:
        if 'stephanie_start_1' in sol:
            total_duration = sol['stephanie_duration_1'] + sol['john_duration_1']
            if total_duration > max_total_duration:
                max_total_duration = total_duration
                best_solution = ('option1', sol)
        elif 'john_start_2' in sol:
            total_duration = sol['john_duration_2'] + sol['stephanie_duration_2']
            if total_duration > max_total_duration:
                max_total_duration = total_duration
                best_solution = ('option2', sol)
    
    if best_solution:
        option_type, sol = best_solution
        itinerary = []
        
        if option_type == 'option1':
            # Stephanie first, then John
            steph_start = start_time_ref + timedelta(minutes=sol['stephanie_start_1'])
            steph_end = steph_start + timedelta(minutes=sol['stephanie_duration_1'])
            john_start = start_time_ref + timedelta(minutes=sol['john_start_1'])
            john_end = john_start + timedelta(minutes=sol['john_duration_1'])
            
            itinerary.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Stephanie",
                "start_time": steph_start.strftime('%-H:%M'),
                "end_time": steph_end.strftime('%-H:%M')
            })
            itinerary.append({
                "action": "meet",
                "location": "Alamo Square",
                "person": "John",
                "start_time": john_start.strftime('%-H:%M'),
                "end_time": john_end.strftime('%-H:%M')
            })
        else:
            # John first, then Stephanie
            john_start = start_time_ref + timedelta(minutes=sol['john_start_2'])
            john_end = john_start + timedelta(minutes=sol['john_duration_2'])
            steph_start = start_time_ref + timedelta(minutes=sol['stephanie_start_2'])
            steph_end = steph_start + timedelta(minutes=sol['stephanie_duration_2'])
            
            itinerary.append({
                "action": "meet",
                "location": "Alamo Square",
                "person": "John",
                "start_time": john_start.strftime('%-H:%M'),
                "end_time": john_end.strftime('%-H:%M')
            })
            itinerary.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Stephanie",
                "start_time": steph_start.strftime('%-H:%M'),
                "end_time": steph_end.strftime('%-H:%M')
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        result = {"itinerary": []}
        print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()