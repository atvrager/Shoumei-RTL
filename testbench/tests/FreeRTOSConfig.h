#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

/* Shoumei CPU: RV32IM, M-mode only, CLINT at 0x02000000 */

/* Scheduler */
#define configUSE_PREEMPTION                    1
#define configUSE_IDLE_HOOK                     0
#define configUSE_TICK_HOOK                     0
#define configTICK_RATE_HZ                      100
#define configMAX_PRIORITIES                    5
#define configMINIMAL_STACK_SIZE                128
#define configMAX_TASK_NAME_LEN                 16
#define configUSE_16_BIT_TICKS                  0
#define configIDLE_SHOULD_YIELD                 1

/* Memory */
#define configTOTAL_HEAP_SIZE                   ( ( size_t ) ( 4 * 1024 ) )
#define configAPPLICATION_ALLOCATED_HEAP        1

/* No mutexes/semaphores/timers needed for basic demo */
#define configUSE_MUTEXES                       0
#define configUSE_RECURSIVE_MUTEXES             0
#define configUSE_COUNTING_SEMAPHORES           0
#define configUSE_TIMERS                        0
#define configQUEUE_REGISTRY_SIZE               0
#define configUSE_QUEUE_SETS                    0

/* No coroutines */
#define configUSE_CO_ROUTINES                   0

/* Hook functions */
#define configCHECK_FOR_STACK_OVERFLOW          0
#define configUSE_MALLOC_FAILED_HOOK            0

/* Run time stats - disabled */
#define configGENERATE_RUN_TIME_STATS           0
#define configUSE_TRACE_FACILITY                0
#define configUSE_STATS_FORMATTING_FUNCTIONS    0

/* Optional functions */
#define INCLUDE_vTaskPrioritySet                0
#define INCLUDE_uxTaskPriorityGet               0
#define INCLUDE_vTaskDelete                     0
#define INCLUDE_vTaskSuspend                    0
#define INCLUDE_vTaskDelayUntil                 0
#define INCLUDE_vTaskDelay                      1
#define INCLUDE_xTaskGetSchedulerState          0

/* ISR stack */
#define configISR_STACK_SIZE_WORDS              256

/* CLINT timer addresses - Shoumei CLINT at 0x02000000 */
#define configMTIME_BASE_ADDRESS                ( 0x0200BFF8UL )
#define configMTIMECMP_BASE_ADDRESS             ( 0x02004000UL )

/* CPU clock = 1 (mtime increments every cycle in our CLINT) */
#define configCPU_CLOCK_HZ                      100000

/* No FPU/VPU context save for now */
#define configENABLE_FPU                        0
#define configENABLE_VPU                        0

/* Disable CLZ-based priority selection (needs __clzsi2 from libgcc) */
#define configUSE_PORT_OPTIMISED_TASK_SELECTION 0

/* Assert */
#define configASSERT( x )   if( ( x ) == 0 ) { for( ;; ); }

#endif /* FREERTOS_CONFIG_H */
