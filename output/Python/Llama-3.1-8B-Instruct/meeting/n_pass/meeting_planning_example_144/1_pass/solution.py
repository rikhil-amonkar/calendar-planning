import json
from datetime import datetime, timedelta

def calculate_travel_time(origin, destination, travel_times):
    if origin == 'The Castro' and destination == 'Mission District':
        return 7
    elif origin == 'The Castro' and destination == 'Financial District':
        return 20
    elif origin == 'Mission District' and destination == 'The Castro':
        return 7
    elif origin == 'Mission District' and destination == 'Financial District':
        return 17
    elif origin == 'Financial District' and destination == 'The Castro':
        return 23
    elif origin == 'Financial District' and destination == 'Mission District':
        return 17

def compute_meeting_schedule(arrival_time, laura_constraints, anthony_constraints, travel_times):
    arrival_hour = int(arrival_time[:2])
    arrival_minute = int(arrival_time[3:])

    # Convert constraints to minutes
    laura_start = int(laura_constraints['start_time'][:2]) * 60 + int(laura_constraints['start_time'][3:])
    laura_end = int(laura_constraints['end_time'][:2]) * 60 + int(laura_constraints['end_time'][3:])
    anthony_start = int(anthony_constraints['start_time'][:2]) * 60 + int(anthony_constraints['start_time'][3:])
    anthony_end = int(anthony_constraints['end_time'][:2]) * 60 + int(anthony_constraints['end_time'][3:])

    # Calculate earliest possible meeting with Laura
    laura_meeting_start = max(arrival_hour * 60 + arrival_minute, laura_start)
    laura_meeting_end = laura_meeting_start + 75

    # Calculate earliest possible meeting with Anthony
    anthony_meeting_start = max(arrival_hour * 60 + arrival_minute, anthony_start)
    anthony_meeting_end = anthony_meeting_start + 30

    # Calculate travel time to Laura
    travel_time_to_laura = calculate_travel_time('The Castro', 'Mission District', travel_times)

    # Calculate travel time to Anthony
    travel_time_to_anthony = calculate_travel_time('The Castro', 'Financial District', travel_times)

    # Check if it's possible to meet both Laura and Anthony
    if laura_meeting_start < laura_end and anthony_meeting_start < anthony_end:
        # Check if it's possible to meet Laura first and then Anthony
        if laura_meeting_end + travel_time_to_anthony <= anthony_start:
            # Calculate the end time after meeting Laura and traveling to Anthony
            end_time = laura_meeting_end + travel_time_to_anthony
            # Check if it's possible to meet Anthony after meeting Laura
            if end_time + 30 <= anthony_start:
                # Create the itinerary
                itinerary = [
                    {'action':'meet', 'location': 'Mission District', 'person': 'Laura','start_time': f"{laura_meeting_start // 60:02d}:{laura_meeting_start % 60:02d}", 'end_time': f"{laura_meeting_end // 60:02d}:{laura_meeting_end % 60:02d}"},
                    {'action': 'travel', 'location': 'The Castro', 'person': '','start_time': f"{laura_meeting_end // 60:02d}:{laura_meeting_end % 60:02d}", 'end_time': f"{(laura_meeting_end // 60 + 1) % 24:02d}:{(laura_meeting_end % 60 + travel_time_to_anthony) % 60:02d}"},
                    {'action':'meet', 'location': 'Financial District', 'person': 'Anthony','start_time': f"{(laura_meeting_end // 60 + 1) % 24:02d}:{(laura_meeting_end % 60 + travel_time_to_anthony) % 60:02d}", 'end_time': f"{((laura_meeting_end // 60 + 1) % 24 + 1):02d}:{(((laura_meeting_end % 60 + travel_time_to_anthony) % 60) + 30) % 60:02d}"}
                ]
            else:
                # Create the itinerary with only meeting Laura
                itinerary = [
                    {'action':'meet', 'location': 'Mission District', 'person': 'Laura','start_time': f"{laura_meeting_start // 60:02d}:{laura_meeting_start % 60:02d}", 'end_time': f"{laura_meeting_end // 60:02d}:{laura_meeting_end % 60:02d}"}
                ]
        # Check if it's possible to meet Anthony first and then Laura
        elif anthony_meeting_end + travel_time_to_laura <= laura_start:
            # Calculate the end time after meeting Anthony and traveling to Laura
            end_time = anthony_meeting_end + travel_time_to_laura
            # Check if it's possible to meet Laura after meeting Anthony
            if end_time + 75 <= laura_start:
                # Create the itinerary
                itinerary = [
                    {'action':'meet', 'location': 'Financial District', 'person': 'Anthony','start_time': f"{anthony_meeting_start // 60:02d}:{anthony_meeting_start % 60:02d}", 'end_time': f"{anthony_meeting_end // 60:02d}:{anthony_meeting_end % 60:02d}"},
                    {'action': 'travel', 'location': 'The Castro', 'person': '','start_time': f"{anthony_meeting_end // 60:02d}:{anthony_meeting_end % 60:02d}", 'end_time': f"{(anthony_meeting_end // 60 + 1) % 24:02d}:{(anthony_meeting_end % 60 + travel_time_to_laura) % 60:02d}"},
                    {'action':'meet', 'location': 'Mission District', 'person': 'Laura','start_time': f"{(anthony_meeting_end // 60 + 1) % 24:02d}:{(anthony_meeting_end % 60 + travel_time_to_laura) % 60:02d}", 'end_time': f"{((anthony_meeting_end // 60 + 1) % 24 + 1):02d}:{(((anthony_meeting_end % 60 + travel_time_to_laura) % 60) + 75) % 60:02d}"}
                ]
            else:
                # Create the itinerary with only meeting Anthony
                itinerary = [
                    {'action':'meet', 'location': 'Financial District', 'person': 'Anthony','start_time': f"{anthony_meeting_start // 60:02d}:{anthony_meeting_start % 60:02d}", 'end_time': f"{anthony_meeting_end // 60:02d}:{anthony_meeting_end % 60:02d}"}
                ]
        else:
            # Create the itinerary with only meeting Laura
            itinerary = [
                {'action':'meet', 'location': 'Mission District', 'person': 'Laura','start_time': f"{laura_meeting_start // 60:02d}:{laura_meeting_start % 60:02d}", 'end_time': f"{laura_meeting_end // 60:02d}:{laura_meeting_end % 60:02d}"}
            ]
    else:
        # Create the itinerary with no meetings
        itinerary = []

    return itinerary

def main():
    travel_times = {
        'The Castro to Mission District': 7,
        'The Castro to Financial District': 20,
        'Mission District to The Castro': 7,
        'Mission District to Financial District': 17,
        'Financial District to The Castro': 23,
        'Financial District to Mission District': 17
    }

    arrival_time = '09:00'
    laura_constraints = {'start_time': '12:15', 'end_time': '19:45'}
    anthony_constraints = {'start_time': '12:30', 'end_time': '14:45'}

    meeting_schedule = compute_meeting_schedule(arrival_time, laura_constraints, anthony_constraints, travel_times)

    print(json.dumps({'itinerary': meeting_schedule}, indent=4))

if __name__ == "__main__":
    main()