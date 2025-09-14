import json
from z3 import Optimize, Int, If, sat

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Constants (all times are in minutes after midnight)
    arrival_alamo = 9 * 60              # 9:00 AM = 540 minutes
    travel_alamo_to_richmond = 12       # minutes from Alamo Square to Richmond District
    timothy_avail_start = 20 * 60 + 45    # 20:45 = 1245 minutes
    timothy_avail_end = 21 * 60 + 30      # 21:30 = 1290 minutes
    required_meeting_duration = 45      # minimum meeting duration in minutes

    # Create an optimizer instance
    opt = Optimize()

    # Decision variables
    departure = Int("departure")        # time to leave Alamo Square (in minutes)
    meeting_start = Int("meeting_start")  # meeting start time with Timothy (in minutes)
    meeting_end = Int("meeting_end")      # meeting end time (in minutes)

    # Constraint 1: We cannot leave Alamo Square before arriving (9:00 AM)
    opt.add(departure >= arrival_alamo)

    # Constraint 2: The meeting can only start when Timothy is available.
    # If you arrive at Richmond District before Timothy is available, you must wait.
    opt.add(meeting_start == If(departure + travel_alamo_to_richmond < timothy_avail_start,
                                timothy_avail_start,
                                departure + travel_alamo_to_richmond))
    
    # Constraint 3: Meeting must last at least the required duration.
    opt.add(meeting_end == meeting_start + required_meeting_duration)
    
    # Constraint 4: The meeting must end by the end of Timothy's availability.
    opt.add(meeting_end <= timothy_avail_end)

    # Constraint 5: If you arrive after Timothy is available,
    # then you must still be able to meet him for the required duration.
    # That is, (departure + travel time) + required duration must be within his availability.
    opt.add(If(departure + travel_alamo_to_richmond >= timothy_avail_start,
               departure <= timothy_avail_end - required_meeting_duration - travel_alamo_to_richmond,
               True))
    
    # Objective: maximize departure time from Alamo Square.
    # This gives you maximum free time in the morning while still being on time for a full meeting.
    opt.maximize(departure)

    if opt.check() == sat:
        model = opt.model()
        dep_val = model[departure].as_long()
        meet_start_val = model[meeting_start].as_long()
        meet_end_val = model[meeting_end].as_long()
        
        itinerary = [
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Timothy",
                "start_time": minutes_to_time(meet_start_val),
                "end_time": minutes_to_time(meet_end_val)
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No valid schedule found."}))

if __name__ == '__main__':
    main()