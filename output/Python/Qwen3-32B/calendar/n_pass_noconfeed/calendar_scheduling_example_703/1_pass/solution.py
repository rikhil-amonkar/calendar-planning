def get_free_intervals(busy_intervals, work_start=540, work_end=1020):
                            sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
                            free = []
                            prev_end = work_start
                            for start, end in sorted_busy:
                                if start > prev_end:
                                    free.append((prev_end, start))
                                prev_end = max(prev_end, end)
                            if prev_end < work_end:
                                free.append((prev_end, work_end))
                            return free

                        def find_overlapping_intervals(intervals1, intervals2):
                            overlapping = []
                            for i1 in intervals1:
                                for i2 in intervals2:
                                    s1, e1 = i1
                                    s2, e2 = i2
                                    start = max(s1, s2)
                                    end = min(e1, e2)
                                    if start < end:
                                        overlapping.append((start, end))
                            return overlapping

                        # Define busy intervals for each day and participant
                        # Stephanie's busy intervals
                        stephanie_mon_buses = [(570, 600), (630, 660), (690, 720), (840, 870)]
                        stephanie_tue_buses = [(720, 780)]
                        stephanie_wed_buses = [(540, 600), (780, 840)]

                        # Betty's busy intervals
                        betty_mon_buses = [(540, 600), (660, 690), (870, 900), (930, 960)]
                        betty_tue_buses = [(540, 570), (690, 720), (750, 870), (930, 960)]
                        betty_wed_buses = [(600, 690), (720, 840), (870, 1020)]

                        days_in_order = ['Tuesday', 'Wednesday', 'Monday']

                        for day in days_in_order:
                            if day == 'Monday':
                                stephanie_buses = stephanie_mon_buses
                                betty_buses = betty_mon_buses
                                betty_work_end = 1020
                            elif day == 'Tuesday':
                                stephanie_buses = stephanie_tue_buses
                                betty_buses = betty_tue_buses
                                betty_work_end = 750  # 12:30 PM
                            elif day == 'Wednesday':
                                stephanie_buses = stephanie_wed_buses
                                betty_buses = betty_wed_buses
                                betty_work_end = 1020

                            # Stephanie's work_end is always 1020
                            stephanie_free = get_free_intervals(stephanie_buses, 540, 1020)
                            betty_free = get_free_intervals(betty_buses, 540, betty_work_end)

                            overlapping = find_overlapping_intervals(stephanie_free, betty_free)

                            for interval in overlapping:
                                start, end = interval
                                if end - start >= 60:
                                    # Found a suitable interval
                                    meeting_start = start
                                    meeting_end = start + 60
                                    # Convert to time strings
                                    def to_time(minutes):
                                        h = minutes // 60
                                        m = minutes % 60
                                        return f"{h:02d}:{m:02d}"
                                    start_time = to_time(meeting_start)
                                    end_time = to_time(meeting_end)
                                    print(f"{start_time}:{end_time} {day}")
                                    exit()