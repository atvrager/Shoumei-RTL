/*
 * FreeRTOS demo for Shoumei CPU.
 * Two tasks alternate printing characters, demonstrating preemptive scheduling.
 * After enough ticks, signals PASS via tohost.
 */
#include "FreeRTOS.h"
#include "task.h"

/* Heap in .noinit section — no need to zero 4KB during BSS clear */
__attribute__((section(".noinit")))
uint8_t ucHeap[configTOTAL_HEAP_SIZE];

/* Shoumei testbench I/O - symbols from linker script */
extern volatile unsigned int tohost;
extern volatile unsigned int putchar_addr;

static void put_char(char c)
{
    putchar_addr = (unsigned int)c;
}

static void put_str(const char *s)
{
    while (*s)
        put_char(*s++);
}

/* Shared counter incremented by tasks */
static volatile int task_a_count = 0;
static volatile int task_b_count = 0;

static void vTaskA(void *pvParameters)
{
    (void)pvParameters;
    for (;;) {
        put_char('A');
        task_a_count++;
        /* Check if we've run enough to declare success */
        if (task_a_count >= 3 && task_b_count >= 3) {
            put_char('\n');
            put_str("PASS\n");
            tohost = 1;
            for (;;);
        }
        vTaskDelay(1);  /* Yield for 1 tick */
    }
}

/* Debug probe: store delay arg to a known address before calling vTaskDelay */
static volatile unsigned int *debug_probe = (volatile unsigned int *)0x3f008;

static void vTaskB(void *pvParameters)
{
    (void)pvParameters;
    for (;;) {
        put_char('B');
        task_b_count++;
        *debug_probe = 0xDEAD0001;  /* marker: about to call vTaskDelay(1) */
        vTaskDelay(1);
    }
}

int main(void)
{
    put_str("FreeRTOS demo start\n");

    xTaskCreate(vTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL, 2, NULL);
    xTaskCreate(vTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL, 2, NULL);

    vTaskStartScheduler();

    /* Should never reach here */
    put_str("FAIL: scheduler returned\n");
    tohost = 1;
    for (;;);
}

/* FreeRTOS requires this for configASSERT failures and stack overflow */
void vApplicationStackOverflowHook(TaskHandle_t xTask, char *pcTaskName)
{
    (void)xTask;
    (void)pcTaskName;
    for (;;);
}
