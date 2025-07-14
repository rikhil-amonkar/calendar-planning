from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times
    # Joseph (Russian Hill)
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')

    # Nancy (Alamo Square)
    nancy_start = Int('nancy_start')
    nancy_end = Int('nancy_end')

    # Jason (North Beach)
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')

    # Jeffrey (Financial District)
    jeffrey_start = Int('jeffrey_start')
    jeffrey_end = Int('jeffrey_end')

    # Convert all times to minutes since 9:00 AM (540 minutes since midnight)
    arrival_time = 540  # 9:00 AM in minutes since midnight

    # Friends' availability windows in minutes since midnight
    joseph_available_start = 510  # 8:30 AM
    joseph_available_end = 1095    # 7:15 PM
    nancy_available_start = 660    # 11:00 AM
    nancy_available_end = 960      # 4:00 PM
    jason_available_start = 1065   # 4:45 PM
    jason_available_end = 1305     # 9:45 PM
    jeffrey_available_start = 630  # 10:30 AM
    jeffrey_available_end = 945    # 3:45 PM

    # Minimum meeting durations in minutes
    joseph_min_duration = 60
    nancy_min_duration = 90
    jason_min_duration = 15
    jeffrey_min_duration = 45

    # Travel times from each location to others (in minutes)
    # From Bayview (starting point)
    bayview_to_russian_hill = 23
    bayview_to_alamo_square = 16
    bayview_to_north_beach = 21
    bayview_to_financial_district = 19

    # From Russian Hill
    russian_hill_to_alamo_square = 15
    russian_hill_to_north_beach = 5
    russian_hill_to_financial_district = 11

    # From Alamo Square
    alamo_square_to_russian_hill = 13
    alamo_square_to_north_beach = 15
    alamo_square_to_financial_district = 17

    # From North Beach
    north_beach_to_russian_hill = 4
    north_beach_to_alamo_square = 16
    north_beach_to_financial_district = 8

    # From Financial District
    financial_district_to_russian_hill = 10
    financial_district_to_alamo_square = 17
    financial_district_to_north_beach = 7

    # Constraints for each meeting
    # Joseph constraints
    s.add(joseph_start >= joseph_available_start)
    s.add(joseph_end <= joseph_available_end)
    s.add(joseph_end - joseph_start >= joseph_min_duration)

    # Nancy constraints
    s.add(nancy_start >= nancy_available_start)
    s.add(nancy_end <= nancy_available_end)
    s.add(nancy_end - nancy_start >= nancy_min_duration)

    # Jason constraints
    s.add(jason_start >= jason_available_start)
    s.add(jason_end <= jason_available_end)
    s.add(jason_end - jason_start >= jason_min_duration)

    # Jeffrey constraints
    s.add(jeffrey_start >= jeffrey_available_start)
    s.add(jeffrey_end <= jeffrey_available_end)
    s.add(jeffrey_end - jeffrey_start >= jeffrey_min_duration)

    # The first meeting must start after arrival_time plus travel time from Bayview
    # We need to determine the order of meetings to account for travel times
    # To simplify, we'll assume a specific order and adjust if necessary
    # Let's try the order: Jeffrey -> Nancy -> Joseph -> Jason

    # Jeffrey is first
    s.add(jeffrey_start >= arrival_time + bayview_to_financial_district)

    # Nancy is after Jeffrey
    s.add(nancy_start >= jeffrey_end + financial_district_to_alamo_square)

    # Joseph is after Nancy
    s.add(joseph_start >= nancy_end + alamo_square_to_russian_hill)

    # Jason is after Joseph
    s.add(jason_start >= joseph_end + russian_hill_to_north_beach)

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        print(f"Meet Jeffrey:")
        jeffrey_s = m.evaluate(jeffrey_start).as_long()
        jeffrey_e = m.evaluate(jeffrey_end).as_long()
        print(f"  Start: {jeffrey_s // 60}:{jeffrey_s % 60:02d}, End: {jeffrey_e // 60}:{jeffrey_e % 60:02d}")
        print(f"Meet Nancy:")
        nancy_s = m.evaluate(nancy_start).as_long()
        nancy_e = m.evaluate(nancy_end).as_long()
        print(f"  Start: {nancy_s // 60}:{nancy_s % 60:02d}, End: {nancy_e // 60}:{nancy_e % 60:02d}")
        print(f"Meet Joseph:")
        joseph_s = m.evaluate(joseph_start).as_long()
        joseph_e = m.evaluate(joseph_end).as_long()
        print(f"  Start: {joseph_s // 60}:{joseph_s % 60:02d}, End: {joseph_e // 60}:{joseph_e % 60:02d}")
        print(f"Meet Jason:")
        jason_s = m.evaluate(jason_start).as_long()
        jason_e = m.evaluate(jason_end).as_long()
        print(f"  Start: {jason_s // 60}:{jason_s % 60:02d}, End: {jason_e // 60}:{jason_e % 60:02d}")
    else:
        print("No feasible schedule found with the given order. Trying a different order...")
        # Try a different order: Nancy -> Jeffrey -> Joseph -> Jason
        s.reset()
        s.add(joseph_start >= joseph_available_start)
        s.add(joseph_end <= joseph_available_end)
        s.add(joseph_end - joseph_start >= joseph_min_duration)
        s.add(nancy_start >= nancy_available_start)
        s.add(nancy_end <= nancy_available_end)
        s.add(nancy_end - nancy_start >= nancy_min_duration)
        s.add(jason_start >= jason_available_start)
        s.add(jason_end <= jason_available_end)
        s.add(jason_end - jason_start >= jason_min_duration)
        s.add(jeffrey_start >= jeffrey_available_start)
        s.add(jeffrey_end <= jeffrey_available_end)
        s.add(jeffrey_end - jeffrey_start >= jeffrey_min_duration)

        # Nancy is first
        s.add(nancy_start >= arrival_time + bayview_to_alamo_square)

        # Jeffrey is after Nancy
        s.add(jeffrey_start >= nancy_end + alamo_square_to_financial_district)

        # Joseph is after Jeffrey
        s.add(joseph_start >= jeffrey_end + financial_district_to_russian_hill)

        # Jason is after Joseph
        s.add(jason_start >= joseph_end + russian_hill_to_north_beach)

        if s.check() == sat:
            m = s.model()
            print("Optimal Schedule:")
            print(f"Meet Nancy:")
            nancy_s = m.evaluate(nancy_start).as_long()
            nancy_e = m.evaluate(nancy_end).as_long()
            print(f"  Start: {nancy_s // 60}:{nancy_s % 60:02d}, End: {nancy_e // 60}:{nancy_e % 60:02d}")
            print(f"Meet Jeffrey:")
            jeffrey_s = m.evaluate(jeffrey_start).as_long()
            jeffrey_e = m.evaluate(jeffrey_end).as_long()
            print(f"  Start: {jeffrey_s // 60}:{jeffrey_s % 60:02d}, End: {jeffrey_e // 60}:{jeffrey_e % 60:02d}")
            print(f"Meet Joseph:")
            joseph_s = m.evaluate(joseph_start).as_long()
            joseph_e = m.evaluate(joseph_end).as_long()
            print(f"  Start: {joseph_s // 60}:{joseph_s % 60:02d}, End: {joseph_e // 60}:{joseph_e % 60:02d}")
            print(f"Meet Jason:")
            jason_s = m.evaluate(jason_start).as_long()
            jason_e = m.evaluate(jason_end).as_long()
            print(f"  Start: {jason_s // 60}:{jason_s % 60:02d}, End: {jason_e // 60}:{jason_e % 60:02d}")
        else:
            print("No feasible schedule found with any order.")

solve_scheduling()