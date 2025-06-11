def main():
    # Define possible start times in minutes from 9:00 (0 = 9:00, 30 = 9:30, etc.)
    possible_starts = [0, 30, 60, 90, 120, 150, 180, 210, 240, 270, 300, 330, 360, 390, 420, 450]
    
    # Jack's available start times (11:30 to 16:30)
    jack_set = {150, 180, 210, 240, 270, 300, 330, 360, 390, 420, 450}
    # Madison is available at all times
    madison_set = set(possible_starts)
    # Rachel's available start times (excludes 12:00)
    rachel_set = {0, 30, 60, 90, 120, 210, 240, 270, 300, 330, 360, 390, 420, 450}
    # Douglas is available at all times
    douglas_set = set(possible_starts)
    # Ryan's available start times (excludes 9:00)
    ryan_set = {30, 60, 90, 120, 150, 180, 210, 240, 270, 300, 330, 360, 390, 420, 450}
    
    # Find common available time across all participants
    common_times = jack_set & madison_set & rachel_set & douglas_set & ryan_set
    
    if common_times:
        # Find earliest time
        start_min = min(common_times)
        # Convert minutes to time format
        hour = 9 + start_min // 60
        minute = start_min % 60
        print(f"{hour}:{minute:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()