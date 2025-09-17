def test_extract_answer_basic():
    from iterative_smt_refinement_enhanced import extract_answer_basic

    gold_examples = [
        # Well-formatted calendar answer
        ("SOLUTION:\nDay: Monday\nStart Time: 13:00\nEnd Time: 13:30", "calendar"),
        # Natural language calendar answer
        ("Here is the proposed time: Monday, 13:00 - 13:30", "calendar"),
        # Specific example 398 gold answer
        ("Here is the proposed time: Monday, 13:00 - 13:30 ", "calendar"),
        # Empty string
        ("", "calendar"),
        # Well-formatted trip answer
        ('{"itinerary": [{"day_range": "Day 1-3", "place": "Venice"}, {"day_range": "Day 3-6", "place": "Vienna"}]}', "trip"),
        # Natural language trip answer
        ("You will be in Venice from Day 1-3, then in Vienna from Day 3-6.", "trip"),
        # Well-formatted meeting answer
        ("Meet David at Office from 13:00 to 14:00", "meeting"),
        # Natural language meeting answer
        ("David: from 1pm to 2pm", "meeting"),
    ]

    for gold_answer, task in gold_examples:
        print(f"Testing gold answer for task '{task}':")
        print(gold_answer)
        try:
            parsed_result = extract_answer_basic(gold_answer, task)
            print(f"Parsed result: {parsed_result}")
        except Exception as e:
            print(f"Error: {e}")
        print("-" * 40)

if __name__ == "__main__":
    test_extract_answer_basic() 