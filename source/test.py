import ast
import re

def format_python_code(code_str):
    # Replace escaped newlines and other escaped characters
    formatted_code = code_str.encode().decode('unicode_escape')
    
    try:
        # Parse the formatted string into an AST (Abstract Syntax Tree)
        parsed_code = ast.parse(formatted_code)
        # Convert the AST back into formatted Python code
        formatted_code = re.sub(r'\n{2,}', '\n\n', formatted_code)  # Normalize extra newlines
        formatted_code = re.sub(r'\s+\n', '\n', formatted_code)  # Remove unnecessary leading spaces
        formatted_code = re.sub(r'\t', '    ', formatted_code)  # Replace tabs with spaces
        return formatted_code
    except SyntaxError as e:
        return f"Syntax Error: {e}"

# Example usage
raw_code = """from datetime import datetime, timedelta\\n\\n\\n# Define a class to represent a time slot\\nclass TimeSlot:\\n    def __init__(self, start_time, end_time):\\n        self.start_time = start_time\\n        self.end_time = end_time\\n\\n\\n# Define the existing schedules of each participant\\nraymond_schedule = [\\n    TimeSlot(datetime(2024, 7, 29, 9, 0), datetime(2024, 7, 29, 9, 30)),\\n    TimeSlot(datetime(2024, 7, 29, 11, 30), datetime(2024, 7, 29, 12, 0)),\\n    TimeSlot(datetime(2024, 7, 29, 13, 0), datetime(2024, 7, 29, 13, 30)),\\n    TimeSlot(datetime(2024, 7, 29, 15, 0), datetime(2024, 7, 29, 15, 30)),\\n]\\n\\nbilly_schedule = [\\n    TimeSlot(datetime(2024, 7, 29, 10, 0), datetime(2024, 7, 29, 10, 30)),\\n    TimeSlot(datetime(2024, 7, 29, 12, 0), datetime(2024, 7, 29, 13, 0)),\\n    TimeSlot(datetime(2024, 7, 29, 16, 30), datetime(2024, 7, 29, 17, 0)),\\n]\\n"""

formatted_code = format_python_code(raw_code)
print(formatted_code)