from z3 import *
import json

def main():
    # Convert all times to minutes from midnight
    start_sunset = 9 * 60  # 9:00 AM

    # Availability times in minutes
    michelle_start = 8 * 60 + 15  # 8:15 AM
    michelle_end = 14 * 60         # 2:00 PM
    robert_start = 9 * 60          # 9:00 AM
    robert_end = 13 * 60 + 45      # 1:45 PM
    george_start = 10 * 60 + 30    # 10:30 AM
    george_end = 18 * 60 + 45      # 6:45 PM
    william_start = 18 * 60 + 30   # 6:30 PM
    william_end = 20 * 60 + 45     # 8:45 PM

    # Travel times from Sunset District to each location
    travel_sunset = {
        0: 30,  # Michelle (Chinatown)
        1: 29,  # Robert (Fisherman's Wharf)
        2: 16   # George (Presidio)
    }

    # Travel times between locations (using indices: 0=Michelle, 1=Robert, 2=George)
    travel_between = {
        (0, 1): 8,   # Michelle to Robert
        (0, 2): 19,  # Michelle to George
        (1, 0): 12,  # Robert to Michelle
        (1, 2): 17,  # Robert to George
        (2, 0): 21,  # George to Michelle
        (2, 1): 19   # George to Robert
    }

    # Travel times from each location to Russian Hill (William)
    travel_to_rh = {
        0: 7,  # Michelle
        1: 7,  # Robert
        2: 14  # George
    }

    # Meeting durations in minutes
    durations = {
        0: 15,  # Michelle
        1: 30,  # Robert
        2: 30,  # George
        'William': 105
    }

    # Create Z3 variables for start times of the three meetings
    start_m = Real('start_m')  # Michelle
    start_r = Real('start_r')  # Robert
    start_g = Real('start_g')  # George
    start_w = Real('start_w')  # William

    # Order variables: which meeting is first, second, third? (0=Michelle, 1=Robert, 2=George)
    order0 = Int('order0')
    order1 = Int('order1')
    order2 = Int('order2')

    s = Solver()

    # Constraints on order: distinct and in [0,1,2]
    s.add(order0 >= 0, order0 <= 2)
    s.add(order1 >= 0, order1 <= 2)
    s.add(order2 >= 0, order2 <= 2)
    s.add(Distinct(order0, order1, order2))

    # First meeting: starts at Sunset start time + travel to that location
    first_start = If(order0 == 0, start_m, If(order0 == 1, start_r, start_g))
    travel0 = If(order0 == 0, travel_sunset[0], 
                 If(order0 == 1, travel_sunset[1], 
                    travel_sunset[2]))
    s.add(first_start == start_sunset + travel0)

    # End time of the first meeting
    end0 = If(order0 == 0, start_m + durations[0],
              If(order0 == 1, start_r + durations[1],
                 start_g + durations[2]))

    # Travel time from first to second meeting
    travel1 = If(And(order0 == 0, order1 == 1), travel_between[(0,1)],
                 If(And(order0 == 0, order1 == 2), travel_between[(0,2)],
                 If(And(order0 == 1, order1 == 0), travel_between[(1,0)],
                 If(And(order0 == 1, order1 == 2), travel_between[(1,2)],
                 If(And(order0 == 2, order1 == 0), travel_between[(2,0)],
                 If(And(order0 == 2, order1 == 1), travel_between[(2,1)],
                  0))))))

    # Second meeting start time
    second_start = If(order1 == 0, start_m, If(order1 == 1, start_r, start_g))
    s.add(second_start >= end0 + travel1)

    # End time of the second meeting
    end1 = If(order1 == 0, start_m + durations[0],
              If(order1 == 1, start_r + durations[1],
                 start_g + durations[2]))

    # Travel time from second to third meeting
    travel2 = If(And(order1 == 0, order2 == 1), travel_between[(0,1)],
                 If(And(order1 == 0, order2 == 2), travel_between[(0,2)],
                 If(And(order1 == 1, order2 == 0), travel_between[(1,0)],
                 If(And(order1 == 1, order2 == 2), travel_between[(1,2)],
                 If(And(order1 == 2, order2 == 0), travel_between[(2,0)],
                 If(And(order1 == 2, order2 == 1), travel_between[(2,1)],
                  0))))))

    # Third meeting start time
    third_start = If(order2 == 0, start_m, If(order2 == 1, start_r, start_g))
    s.add(third_start >= end1 + travel2)

    # End time of the third meeting
    end2 = If(order2 == 0, start_m + durations[0],
              If(order2 == 1, start_r + durations[1],
                 start_g + durations[2]))

    # Travel time from third meeting to William
    travel3 = If(order2 == 0, travel_to_rh[0],
                 If(order2 == 1, travel_to_rh[1],
                    travel_to_rh[2]))
    s.add(start_w >= end2 + travel3)
    s.add(start_w >= william_start)
    end_w = start_w + durations['William']
    s.add(end_w <= william_end)

    # Availability constraints for each meeting
    s.add(start_m >= michelle_start, start_m + durations[0] <= michelle_end)
    s.add(start_r >= robert_start, start_r + durations[1] <= robert_end)
    s.add(start_g >= george_start, start_g + durations[2] <= george_end)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Helper function to convert Z3 Real to integer minutes
        def get_time(var):
            val = m[var]
            if is_algebraic_value(val):
                return val.approx(10).as_long()
            else:
                return val.as_long()

        start_m_val = get_time(start_m)
        end_m_val = start_m_val + durations[0]
        start_r_val = get_time(start_r)
        end_r_val = start_r_val + durations[1]
        start_g_val = get_time(start_g)
        end_g_val = start_g_val + durations[2]
        start_w_val = get_time(start_w)
        end_w_val = start_w_val + durations['William']

        # Get the order
        order0_val = m[order0].as_long()
        order1_val = m[order1].as_long()
        order2_val = m[order2].as_long()

        # Create meetings in chronological order (by their start times in the sequence)
        meetings = []
        # First meeting
        if order0_val == 0:
            meetings.append(('Michelle', start_m_val, end_m_val))
        elif order0_val == 1:
            meetings.append(('Robert', start_r_val, end_r_val))
        else:
            meetings.append(('George', start_g_val, end_g_val))
        # Second meeting
        if order1_val == 0:
            meetings.append(('Michelle', start_m_val, end_m_val))
        elif order1_val == 1:
            meetings.append(('Robert', start_r_val, end_r_val))
        else:
            meetings.append(('George', start_g_val, end_g_val))
        # Third meeting
        if order2_val == 0:
            meetings.append(('Michelle', start_m_val, end_m_val))
        elif order2_val == 1:
            meetings.append(('Robert', start_r_val, end_r_val))
        else:
            meetings.append(('George', start_g_val, end_g_val))
        # William's meeting
        meetings.append(('William', start_w_val, end_w_val))

        # Sort meetings by start time (though they should be in order already, but just in case)
        meetings.sort(key=lambda x: x[1])

        # Convert times to HH:MM format
        def to_hhmm(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        itinerary = []
        for person, start, end in meetings:
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": to_hhmm(start),
                "end_time": to_hhmm(end)
            })

        # Output as JSON
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()