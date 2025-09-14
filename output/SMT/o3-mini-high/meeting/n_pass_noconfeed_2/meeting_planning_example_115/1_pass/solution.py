from z3 import *
import json

def convert_minutes_to_time(minutes):
    # Convert minutes (offset from 9:00) to a 24-hour format string without a leading zero on the hour.
    hour = 9 + (minutes // 60)
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an Optimize object that allows us to maximize total meeting time.
    opt = Optimize()

    # Define integer variables representing the start and end times (in minutes after 9:00) for each meeting.
    c_start = Int('c_start')  # Start time for Carol meeting (Marina District)
    c_end = Int('c_end')      # End time for Carol meeting
    j_start = Int('j_start')  # Start time for Jessica meeting (Pacific Heights)
    j_end = Int('j_end')      # End time for Jessica meeting

    # -----------------------------------------------------------------
    # Constraints for Carol's meeting:
    # Carol is at Marina District from 11:30AM to 3:00PM.
    # In minutes after 9:00AM, 11:30AM is 150 and 3:00PM is 360.
    # You’d like to meet Carol for a minimum of 60 minutes.
    # Also, you start at Richmond District at 9:00 and travel to Marina takes 9 minutes.
    opt.add(c_start >= 150)         # Cannot start before Carol becomes available (11:30)
    opt.add(c_start >= 9)           # Must account for travel from Richmond to Marina (9 minutes); this is automatically satisfied
    opt.add(c_end <= 360)           # Must finish by Carol's departure time (3:00PM)
    opt.add(c_end - c_start >= 60)  # At least 60 minutes with Carol

    # -----------------------------------------------------------------
    # Constraints for Jessica's meeting:
    # Jessica is at Pacific Heights from 3:30PM to 4:45PM.
    # In minutes after 9:00AM, 3:30PM is 390 and 4:45PM is 465.
    # You’d like to meet Jessica for a minimum of 45 minutes.
    # Also, after meeting Carol at Marina District, you travel to Pacific Heights which takes 7 minutes.
    opt.add(j_start >= c_end + 7)   # Must leave Carol's meeting and add travel time (7 minutes)
    opt.add(j_start >= 390)         # Jessica is available starting at 3:30PM
    opt.add(j_end <= 465)           # Jessica is available until 4:45PM
    opt.add(j_end - j_start >= 45)  # At least 45 minutes with Jessica

    # -----------------------------------------------------------------
    # Objective: Maximize total meeting time.
    # This encourages the schedule to use as much of the available window as possible,
    # which indirectly confirms that both meetings can be attended.
    total_meeting_time = (c_end - c_start) + (j_end - j_start)
    opt.maximize(total_meeting_time)

    # Check satisfiability and extract a model if a solution is found.
    if opt.check() == sat:
        model = opt.model()
        c_start_val = model[c_start].as_long()
        c_end_val = model[c_end].as_long()
        j_start_val = model[j_start].as_long()
        j_end_val = model[j_end].as_long()

        itinerary = [
            {
                "action": "meet",
                "location": "Marina District",
                "person": "Carol",
                "start_time": convert_minutes_to_time(c_start_val),
                "end_time": convert_minutes_to_time(c_end_val)
            },
            {
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Jessica",
                "start_time": convert_minutes_to_time(j_start_val),
                "end_time": convert_minutes_to_time(j_end_val)
            }
        ]
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()