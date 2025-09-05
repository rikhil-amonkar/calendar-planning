import json
from z3 import Optimize, Int, sat

def minutes_to_timestr(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()

    # Fixed arrival: North Beach at 9:00AM = 540 minutes after midnight.
    nb_arrival = 540

    # Travel times in minutes:
    travel_NB_to_PH = 8
    travel_NB_to_EB = 6
    travel_PH_to_NB = 9
    travel_PH_to_EB = 10
    travel_EB_to_NB = 5
    travel_EB_to_PH = 11

    # Mark's meeting constraints at Embarcadero:
    # Available from 13:00 (780) to 17:45 (1065) and minimum meeting duration is 120 minutes.
    mark_available_start = 13 * 60      # 780 minutes
    mark_available_end = 17 * 60 + 45     # 1065 minutes
    mark_min_duration = 120

    # Karen's meeting constraints at Pacific Heights:
    # Available from 18:45 (1125) to 20:15 (1215) and minimum meeting duration is 90 minutes.
    karen_available_start = 18 * 60 + 45  # 1125 minutes
    karen_available_end = 20 * 60 + 15    # 1215 minutes
    karen_min_duration = 90

    # Define meeting time variables (in minutes after midnight)
    start_M = Int("start_M")  # Mark meeting start time at Embarcadero
    end_M   = Int("end_M")    # Mark meeting end time at Embarcadero
    start_K = Int("start_K")  # Karen meeting start time at Pacific Heights
    end_K   = Int("end_K")    # Karen meeting end time at Pacific Heights

    # Mark meeting constraints:
    opt.add(start_M >= mark_available_start)         # Must not start before 13:00
    opt.add(end_M <= mark_available_end)             # Must finish by 17:45
    opt.add(end_M - start_M >= mark_min_duration)      # At least 120 minutes meeting
    # Also, must not start before arriving at Embarcadero from North Beach.
    opt.add(start_M >= nb_arrival + travel_NB_to_EB)

    # Karen meeting constraints:
    opt.add(start_K >= karen_available_start)          # Cannot start before 18:45
    opt.add(end_K <= karen_available_end)              # Must finish by 20:15
    opt.add(end_K - start_K >= karen_min_duration)       # At least 90 minutes meeting

    # Travel constraint between meetings:
    # After Mark meeting ends at Embarcadero, add travel time to Pacific Heights.
    opt.add(start_K >= end_M + travel_EB_to_PH)

    # For an "optimal" schedule, we want to minimize the waiting time.
    # Waiting before Mark: time gap from arriving at EB to start_M.
    waiting1 = start_M - (nb_arrival + travel_NB_to_EB)
    # Waiting before Karen: time gap from arriving at PH (end_M + travel_EB_to_PH) to start_K.
    waiting2 = start_K - (end_M + travel_EB_to_PH)
    total_waiting = waiting1 + waiting2
    opt.minimize(total_waiting)

    if opt.check() == sat:
        model = opt.model()
        itinerary = [
            {
                "action": "meet",
                "location": "Embarcadero",
                "person": "Mark",
                "start_time": minutes_to_timestr(model[start_M].as_long()),
                "end_time": minutes_to_timestr(model[end_M].as_long())
            },
            {
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Karen",
                "start_time": minutes_to_timestr(model[start_K].as_long()),
                "end_time": minutes_to_timestr(model[end_K].as_long())
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()