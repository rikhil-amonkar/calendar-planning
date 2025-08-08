from z3 import *
import json

def main():
    # Convert all times to minutes from midnight
    # Sunset start time: 9:00 AM -> 540 minutes
    start_sunset = 540

    # Availability end times in minutes
    michelle_end_time = 14 * 60      # 2:00 PM
    robert_end_time = 13 * 60 + 45   # 1:45 PM
    george_start_time = 10 * 60 + 30 # 10:30 AM
    george_end_time = 18 * 60 + 45   # 6:45 PM
    william_start_time = 18 * 60 + 30 # 6:30 PM
    william_end_time = 20 * 60 + 45  # 8:45 PM

    # Travel times from Sunset District to each location (Michelle: Chinatown, Robert: Fisherman's Wharf, George: Presidio)
    travel_sunset = [30, 29, 16]  # [Chinatown, Fisherman's Wharf, Presidio]

    # Travel times between the three locations: [Chinatown, Fisherman's Wharf, Presidio]
    travel_matrix = [
        [0, 8, 19],   # From Chinatown to [Chinatown, Fisherman's Wharf, Presidio]
        [12, 0, 17],   # From Fisherman's Wharf to [Chinatown, Fisherman's Wharf, Presidio]
        [21, 19, 0]    # From Presidio to [Chinatown, Fisherman's Wharf, Presidio]
    ]

    # Travel times from each location to Russian Hill (William)
    travel_to_rh = [7, 7, 14]  # [Chinatown, Fisherman's Wharf, Presidio]

    # Meeting durations in minutes: Michelle (15), Robert (30), George (30)
    durations = [15, 30, 30]

    # Create Z3 variables
    order0 = Int('order0')
    order1 = Int('order1')
    order2 = Int('order2')
    start0 = Real('start0')
    start1 = Real('start1')
    start2 = Real('start2')
    startW = Real('startW')

    s = Solver()

    # Order constraints: distinct and in [0,1,2]
    s.add(Distinct(order0, order1, order2))
    s.add(order0 >= 0, order0 <= 2)
    s.add(order1 >= 0, order1 <= 2)
    s.add(order2 >= 0, order2 <= 2)

    # Start time for the first meeting: after travel from Sunset
    s.add(start0 == start_sunset + travel_sunset[order0])
    end0 = start0 + durations[order0]

    # Second meeting: after travel from the first location
    s.add(start1 == end0 + travel_matrix[order0][order1])
    end1 = start1 + durations[order1]

    # Third meeting: after travel from the second location
    s.add(start2 == end1 + travel_matrix[order1][order2])
    end2 = start2 + durations[order2]

    # William's meeting: after travel from the third location and within availability
    s.add(startW >= end2 + travel_to_rh[order2])
    s.add(startW >= william_start_time)
    endW = startW + 105
    s.add(endW <= william_end_time)

    # Availability constraints for the first three meetings
    # Michelle (0): end time <= 14:00 (840 minutes)
    # Robert (1): end time <= 13:45 (825 minutes)
    # George (2): start time >= 10:30 (630 minutes), end time <= 18:45 (1125 minutes)
    s.add(If(order0 == 0, end0 <= michelle_end_time, 
          If(order0 == 1, end0 <= robert_end_time, 
          If(order0 == 2, And(start0 >= george_start_time, end0 <= george_end_time), True)))
    
    s.add(If(order1 == 0, end1 <= michelle_end_time, 
          If(order1 == 1, end1 <= robert_end_time, 
          If(order1 == 2, And(start1 >= george_start_time, end1 <= george_end_time), True)))
    
    s.add(If(order2 == 0, end2 <= michelle_end_time, 
          If(order2 == 1, end2 <= robert_end_time, 
          If(order2 == 2, And(start2 >= george_start_time, end2 <= george_end_time), True)))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Extract order values
        o0 = m[order0].as_long()
        o1 = m[order1].as_long()
        o2 = m[order2].as_long()
        # Extract start times
        st0 = m[start0].as_fraction().numerator // m[start0].as_fraction().denominator
        st1 = m[start1].as_fraction().numerator // m[start1].as_fraction().denominator
        st2 = m[start2].as_fraction().numerator // m[start2].as_fraction().denominator
        stW = m[startW].as_fraction().numerator // m[startW].as_fraction().denominator
        # Calculate end times
        et0 = st0 + durations[o0]
        et1 = st1 + durations[o1]
        et2 = st2 + durations[o2]
        etW = stW + 105

        # Map order to meetings
        meetings = []
        # First meeting
        if o0 == 0:
            meetings.append(('Michelle', st0, et0))
        elif o0 == 1:
            meetings.append(('Robert', st0, et0))
        elif o0 == 2:
            meetings.append(('George', st0, et0))
        # Second meeting
        if o1 == 0:
            meetings.append(('Michelle', st1, et1))
        elif o1 == 1:
            meetings.append(('Robert', st1, et1))
        elif o1 == 2:
            meetings.append(('George', st1, et1))
        # Third meeting
        if o2 == 0:
            meetings.append(('Michelle', st2, et2))
        elif o2 == 1:
            meetings.append(('Robert', st2, et2))
        elif o2 == 2:
            meetings.append(('George', st2, et2))
        # William's meeting
        meetings.append(('William', stW, etW))

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