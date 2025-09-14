from z3 import Optimize, Int, sat
import json

def minutes_to_time_str(offset):
    # our time variables are in minutes after 9:00.
    total_minutes = 9 * 60 + offset
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Travel times in minutes
    ph_to_presidio = 11         # Pacific Heights -> Presidio
    ph_to_marina = 6            # Pacific Heights -> Marina District (not used in this schedule)
    presidio_to_ph = 11         # Presidio -> Pacific Heights
    presidio_to_marina = 10     # Presidio -> Marina District
    marina_to_ph = 7            # Marina District -> Pacific Heights
    marina_to_presidio = 10     # Marina District -> Presidio

    # Time reference: minutes after 9:00 AM.
    # 9:00 AM -> 0 minutes offset.
    # Jason is available at Presidio from 10:00AM (60) to 4:15PM (435),
    # and the meeting must be at least 90 minutes.
    # Kenneth is available at Marina District from 3:30PM (390) to 4:45PM (465),
    # and the meeting must be at least 45 minutes.

    opt = Optimize()

    # Define meeting time variables (in minutes offset from 9:00)
    jason_start = Int("jason_start")
    jason_end = Int("jason_end")
    kenneth_start = Int("kenneth_start")
    kenneth_end = Int("kenneth_end")

    # Jason's meeting constraints: Must occur when Jason is available.
    opt.add(jason_start >= 60)         # Jason's availability starts at 10:00
    opt.add(jason_end <= 435)            # Jason's availability ends at 16:15
    opt.add(jason_end - jason_start >= 90)  # Minimum meeting duration: 90 minutes

    # Also, you travel from Pacific Heights to Presidio.
    # You arrive at PH at 9:00, travel time is 11 minutes.
    # So realistically, you cannot start meeting earlier than 9:00+11 = 11 minutes, 
    # but Jason's availability already forces jason_start >= 60.
    opt.add(jason_start >= ph_to_presidio)

    # Kenneth's meeting constraints: Must occur when Kenneth is available.
    opt.add(kenneth_start >= 390)       # Kenneth available from 15:30 (390 minutes from 9:00)
    opt.add(kenneth_end <= 465)          # Kenneth available until 16:45 (465 minutes from 9:00)
    opt.add(kenneth_end - kenneth_start >= 45)  # Minimum meeting duration: 45 minutes

    # Travel constraint between meetings:
    # After finishing the meeting with Jason at Presidio, you travel to Marina District.
    # Travel time is presidio_to_marina = 10 minutes.
    opt.add(jason_end + presidio_to_marina <= kenneth_start)

    # To pick an "optimal" schedule (minimizing idle waiting time), we add an objective.
    # Idle waiting at Presidio: waiting from earliest possible meeting start (10:00, offset 60)
    # to the actual start of the meeting with Jason.
    wait_at_presidio = jason_start - 60
    # Idle waiting between meetings: waiting from when you can leave Presidio
    # (jason_end + travel time) until Kenneth's meeting starts.
    wait_between = kenneth_start - (jason_end + presidio_to_marina)
    total_wait = wait_at_presidio + wait_between
    opt.minimize(total_wait)

    # Check for solution
    if opt.check() == sat:
        model = opt.model()
        jason_start_val = model[jason_start].as_long()
        jason_end_val = model[jason_end].as_long()
        kenneth_start_val = model[kenneth_start].as_long()
        kenneth_end_val = model[kenneth_end].as_long()

        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "location": "Presidio",
                    "person": "Jason",
                    "start_time": minutes_to_time_str(jason_start_val),
                    "end_time": minutes_to_time_str(jason_end_val)
                },
                {
                    "action": "meet",
                    "location": "Marina District",
                    "person": "Kenneth",
                    "start_time": minutes_to_time_str(kenneth_start_val),
                    "end_time": minutes_to_time_str(kenneth_end_val)
                }
            ]
        }
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()