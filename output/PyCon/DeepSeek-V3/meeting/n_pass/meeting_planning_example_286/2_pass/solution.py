import json
from constraint import Problem, AllDifferentConstraint

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since 9:00 (540 minutes)"""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (from -> to)
    travel_times = {
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Sunset District'): 26,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Bayview'): 15,
        ('Mission District', 'Sunset District'): 24,
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Sunset District'): 23,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Bayview'): 22
    }
    
    # Convert all times to minutes since 9:00 (540 minutes)
    start_time_min = 540  # 9:00 AM
    
    # Friend constraints in minutes since 9:00
    friend_constraints = {
        'Rebecca': {
            'location': 'Mission District',
            'available_start': time_to_minutes('11:30'),
            'available_end': time_to_minutes('20:15'),
            'min_duration': 120
        },
        'Karen': {
            'location': 'Bayview',
            'available_start': time_to_minutes('12:45'),
            'available_end': time_to_minutes('15:00'),
            'min_duration': 120
        },
        'Carol': {
            'location': 'Sunset District',
            'available_start': time_to_minutes('10:15'),
            'available_end': time_to_minutes('11:45'),
            'min_duration': 30
        }
    }
    
    # Create problem instance
    problem = Problem()
    
    # Define variables for each friend: (start_time, end_time)
    # We'll use minutes since 9:00
    friends = ['Carol', 'Rebecca', 'Karen']
    
    # Add variables for start times (in minutes since 9:00)
    for friend in friends:
        constraints = friend_constraints[friend]
        # Start time must be within available window and allow for minimum duration
        min_start = constraints['available_start']
        max_start = constraints['available_end'] - constraints['min_duration']
        problem.addVariable(f"{friend}_start", range(min_start, max_start + 1))
    
    # Add constraint for end times based on start times and durations
    def set_end_times(carol_start, rebecca_start, karen_start):
        return {
            'Carol_end': carol_start + friend_constraints['Carol']['min_duration'],
            'Rebecca_end': rebecca_start + friend_constraints['Rebecca']['min_duration'],
            'Karen_end': karen_start + friend_constraints['Karen']['min_duration']
        }
    
    problem.addConstraint(set_end_times, ['Carol_start', 'Rebecca_start', 'Karen_start'])
    
    # Add travel time constraints
    def travel_constraint(carol_start, rebecca_start, karen_start):
        # Calculate end times
        carol_end = carol_start + friend_constraints['Carol']['min_duration']
        rebecca_end = rebecca_start + friend_constraints['Rebecca']['min_duration']
        karen_end = karen_start + friend_constraints['Karen']['min_duration']
        
        # We need to find a valid order that accounts for travel times
        meetings = [
            ('Carol', carol_start, carol_end, 'Sunset District'),
            ('Rebecca', rebecca_start, rebecca_end, 'Mission District'), 
            ('Karen', karen_start, karen_end, 'Bayview')
        ]
        
        # Sort by start time to check travel constraints
        meetings_sorted = sorted(meetings, key=lambda x: x[1])
        
        for i in range(len(meetings_sorted) - 1):
            current_meeting = meetings_sorted[i]
            next_meeting = meetings_sorted[i + 1]
            
            # Calculate travel time between locations
            travel_time = travel_times.get(
                (current_meeting[3], next_meeting[3]), 
                travel_times.get(('Union Square', next_meeting[3]))  # Fallback
            )
            
            # Check if there's enough time to travel
            if current_meeting[2] + travel_time > next_meeting[1]:
                return False
        
        return True
    
    problem.addConstraint(travel_constraint, ['Carol_start', 'Rebecca_start', 'Karen_start'])
    
    # Add constraint that meetings cannot overlap (accounting for travel)
    def no_overlap(carol_start, rebecca_start, karen_start):
        # Calculate end times
        carol_end = carol_start + friend_constraints['Carol']['min_duration']
        rebecca_end = rebecca_start + friend_constraints['Rebecca']['min_duration']
        karen_end = karen_start + friend_constraints['Karen']['min_duration']
        
        meetings = [
            ('Carol', carol_start, carol_end),
            ('Rebecca', rebecca_start, rebecca_end),
            ('Karen', karen_start, karen_end)
        ]
        
        # Check all pairs for overlap
        for i in range(len(meetings)):
            for j in range(i + 1, len(meetings)):
                m1_start, m1_end = meetings[i][1], meetings[i][2]
                m2_start, m2_end = meetings[j][1], meetings[j][2]
                
                # Check if meetings overlap
                if not (m1_end <= m2_start or m2_end <= m1_start):
                    return False
        
        return True
    
    problem.addConstraint(no_overlap, ['Carol_start', 'Rebecca_start', 'Karen_start'])
    
    # Try to find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try with reduced meeting times
        for friend in friends:
            friend_constraints[friend]['min_duration'] = max(30, friend_constraints[friend]['min_duration'] - 30)
        
        # Recreate problem with reduced durations
        problem = Problem()
        for friend in friends:
            constraints = friend_constraints[friend]
            min_start = constraints['available_start']
            max_start = constraints['available_end'] - constraints['min_duration']
            problem.addVariable(f"{friend}_start", range(min_start, max_start + 1))
        
        # Update the end time constraint function
        def set_end_times_reduced(carol_start, rebecca_start, karen_start):
            return {
                'Carol_end': carol_start + friend_constraints['Carol']['min_duration'],
                'Rebecca_end': rebecca_start + friend_constraints['Rebecca']['min_duration'],
                'Karen_end': karen_start + friend_constraints['Karen']['min_duration']
            }
        
        problem.addConstraint(set_end_times_reduced, ['Carol_start', 'Rebecca_start', 'Karen_start'])
        problem.addConstraint(travel_constraint, ['Carol_start', 'Rebecca_start', 'Karen_start'])
        problem.addConstraint(no_overlap, ['Carol_start', 'Rebecca_start', 'Karen_start'])
        
        solutions = problem.getSolutions()
    
    if solutions:
        # Use the first valid solution
        solution = solutions[0]
        
        # Calculate end times
        carol_end = solution['Carol_start'] + friend_constraints['Carol']['min_duration']
        rebecca_end = solution['Rebecca_start'] + friend_constraints['Rebecca']['min_duration']
        karen_end = solution['Karen_start'] + friend_constraints['Karen']['min_duration']
        
        # Create itinerary
        itinerary = []
        
        # Add meetings in chronological order
        meetings = [
            {
                'person': 'Carol',
                'location': 'Sunset District', 
                'start': solution['Carol_start'],
                'end': carol_end
            },
            {
                'person': 'Rebecca',
                'location': 'Mission District',
                'start': solution['Rebecca_start'], 
                'end': rebecca_end
            },
            {
                'person': 'Karen', 
                'location': 'Bayview',
                'start': solution['Karen_start'],
                'end': karen_end
            }
        ]
        
        # Sort by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Add travel from Union Square to first meeting
        first_meeting = meetings[0]
        travel_start = start_time_min
        travel_end = start_time_min + travel_times[('Union Square', first_meeting['location'])]
        
        itinerary.append({
            "action": "travel",
            "location": first_meeting['location'],
            "person": "",
            "start_time": minutes_to_time(travel_start),
            "end_time": minutes_to_time(travel_end)
        })
        
        # Add meetings and travel between them
        for i, meeting in enumerate(meetings):
            # Add the meeting
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['person'],
                "start_time": minutes_to_time(meeting['start']),
                "end_time": minutes_to_time(meeting['end'])
            })
            
            # Add travel to next meeting if there is one
            if i < len(meetings) - 1:
                next_meeting = meetings[i + 1]
                travel_time = travel_times.get(
                    (meeting['location'], next_meeting['location']),
                    travel_times.get(('Union Square', next_meeting['location']))
                )
                
                travel_start = meeting['end']
                travel_end = meeting['end'] + travel_time
                
                itinerary.append({
                    "action": "travel",
                    "location": next_meeting['location'],
                    "person": "",
                    "start_time": minutes_to_time(travel_start),
                    "end_time": minutes_to_time(travel_end)
                })
        
        # Output as JSON
        result = {
            "itinerary": itinerary
        }
        
        print(json.dumps(result, indent=2))
    else:
        # No solution found
        print(json.dumps({"itinerary": [], "error": "No valid schedule found"}, indent=2))

if __name__ == "__main__":
    main()